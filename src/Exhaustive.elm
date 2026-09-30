module Exhaustive exposing (Expansion, Frontier, enqueue, estimatedTreeSize, expansionsOf, initialFrontier, next, size)

{-| Walking the whole space of choices a fuzzer can make.

Every fuzzer bottoms out in `rollDice maxValue _`, which draws one integer in
`0..maxValue`. So a fuzzer is a function from a sequence of bounded integers (a
`RandomRun`) to a value, and the set of inputs it can produce is a tree: one
level per draw, `maxValue + 1` children per node. Enumerating that tree
enumerates the fuzzer.

Doing it this way rather than teaching each combinator to list its own values
(the approach sketched in
<https://github.com/elm-explorations/test/issues/188>) has three consequences
worth knowing:

  - No combinator changes. `andThen`, `filter`, `lazy` and recursive fuzzers all
    work, because none of them are involved — they're just consumers of draws.
    `andThen` is where the per-combinator approach gets hard, since its count
    depends on the value drawn before it.
  - Failures still simplify. Enumeration produces real `RandomRun`s, so
    `Simplify` needs no changes at all.
  - It enumerates _choice sequences_, not values. Where the mapping isn't
    injective — `intRange` above its bucketing threshold draws a bucket and then
    a value, `filter` retries, `map` can collapse — the same value is reached more
    than once. That costs redundant work; it never misses anything.


## How a node is expanded

Generating with a prefix yields the run that was taken and the bound at each
position. The other reachable runs that agree with it up to position `i` are
exactly those taking some larger choice at `i`:

    run   = [ 0, 1, 0 ]
    maxes = [ 1, 2, 0 ]

    -> position 0 has alternative 1        -> prefix [ 1 ]
    -> position 1 has alternative 2        -> prefix [ 0, 2 ]
    -> position 2 is forced, no alternative

Each of those prefixes is generated in turn, and yields expansions of its own.
Every run in the tree is reached exactly once, so nothing needs deduplicating.

Expansions are stored per _position_ rather than per child, so a node with a
branching factor of 1000 costs one frontier entry instead of a thousand.

-}

import RandomRun exposing (RandomRun)


{-| One position in a run that still has untried alternatives.
-}
type alias Expansion =
    { prefix : List Int
    , nextAlt : Int
    , maxAlt : Int
    }


{-| Prefixes still waiting to be generated.

A FIFO queue, so the walk proceeds roughly breadth-first. That matters: a
depth-first walk of `Fuzz.list Fuzz.bool` descends `[] -> [False] ->
[False,False] -> ...` forever and never reaches `[False, True]`, because the
tree is infinite in depth but finite in breadth.

-}
type alias Frontier =
    { queue : List Expansion
    , pending : List Expansion
    }


{-| The walk starts from the all-zeros run, which needs no prefix.
-}
initialFrontier : Frontier
initialFrontier =
    { queue = [], pending = [] }


{-| Take the next prefix to generate, if the tree isn't exhausted.
-}
next : Frontier -> Maybe ( List Int, Frontier )
next frontier =
    case frontier.queue of
        [] ->
            case List.reverse frontier.pending of
                [] ->
                    Nothing

                queue ->
                    next { queue = queue, pending = [] }

        expansion :: rest ->
            let
                prefix : List Int
                prefix =
                    expansion.prefix ++ [ expansion.nextAlt ]

                -- Put the position back if it has further alternatives.
                requeued : List Expansion
                requeued =
                    if expansion.nextAlt < expansion.maxAlt then
                        [ { expansion | nextAlt = expansion.nextAlt + 1 } ]

                    else
                        []
            in
            Just
                ( prefix
                , { queue = rest
                  , pending = requeued ++ frontier.pending
                  }
                )


{-| The positions of a freshly generated run that still have alternatives.

`fromIndex` is the length of the prefix that produced this run: earlier
positions were already queued by whoever produced that prefix, and requeuing
them would generate the same runs twice.

-}
expansionsOf : Int -> RandomRun -> RandomRun -> List Expansion
expansionsOf fromIndex run maxes =
    List.map2 Tuple.pair (RandomRun.toList run) (RandomRun.toList maxes)
        |> List.indexedMap (\index ( choice, maxChoice ) -> ( index, choice, maxChoice ))
        |> List.filterMap
            (\( index, choice, maxChoice ) ->
                if index < fromIndex || choice >= maxChoice then
                    Nothing

                else
                    Just
                        { prefix = List.take index (RandomRun.toList run)
                        , nextAlt = choice + 1
                        , maxAlt = maxChoice
                        }
            )


{-| Add newly discovered positions to the frontier.
-}
enqueue : List Expansion -> Frontier -> Frontier
enqueue expansions frontier =
    { frontier | pending = List.foldl (::) frontier.pending expansions }


{-| How many positions are waiting. Used to give up on trees too wide to be
worth walking.
-}
size : Frontier -> Int
size frontier =
    List.length frontier.queue + List.length frontier.pending


{-| Roughly how many distinct choice sequences this fuzzer can produce, from the
bounds recorded on a single generated run.

The product of `max + 1` over the run: each position independently admits that
many choices. Saturates at `limit` rather than computing the true value, which
for something like `Fuzz.int` would overflow into nonsense.

This is an estimate, not a bound. It's exact when every path through the tree has
the same shape, and wrong for fuzzers whose structure depends on values already
drawn -- `andThen`, `list`, recursive fuzzers. That's acceptable because it's only
used to decide whether walking the tree is worth _starting_: guessing too high
means we sample, which is what we do today anyway.

It catches the case a frontier-width limit cannot. `Fuzz.intRange 0 1000` is a
single draw with a thousand alternatives: width 1, size 1001.

-}
estimatedTreeSize : Int -> RandomRun -> Int
estimatedTreeSize limit maxes =
    List.foldl
        (\maxChoice acc ->
            if acc >= limit then
                limit

            else
                min limit (acc * (maxChoice + 1))
        )
        1
        (RandomRun.toList maxes)
