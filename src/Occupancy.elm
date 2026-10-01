module Occupancy exposing
    ( Occupancy
    , childOf
    , empty
    , exhaustedChildren
    , isExhausted
    , isOpen
    , markCovered
    , novelPrefix
    )

{-| What part of a fuzzer's input space has already been covered.

Every fuzzer bottoms out in `rollDice maxValue _`, so the inputs it can produce
form a tree with `maxValue + 1` children per node. This records which subtrees of
that tree have been completely explored, so a draw can decline them.

That one idea does the work of three separate mechanisms:

  - **No duplicates.** A covered leaf is never offered again, so no input is ever
    tested twice — without hashing runs or keeping a set of them.

  - **Early termination.** When the root is covered there is provably nothing
    left to test, whatever run count was requested.

  - **Partial coverage.** The interesting case. Given

        Fuzz.oneOf
            [ Fuzz.map Err Fuzz.string
            , Fuzz.map Ok Fuzz.bool
            ]

    `oneOf` spends half its runs re-testing `Ok True` and `Ok False`. Here the
    `Ok` subtree is covered after two draws and then stops being offered, so its
    share redistributes to `Err` and a defect in the `Err` branch is found about
    twice as fast. Neither whole-tree enumeration nor per-run deduplication gets
    this: the tree is infinite, so there is nothing to enumerate, and the runs
    aren't duplicates until they have already been generated.

The important property is that **conditioning only happens once something is
actually covered**. Until then the draw is exactly the draw that would have
happened anyway, so fuzzers with large domains behave identically — same seed,
same values, no probe, no mode switch.


## Bounding the cost

Tracking everything would cost memory and time proportional to the number of
runs, for fuzzers that can never exhaust anything. Three bounds prevent that: a
limit on how deep coverage is recorded, on how wide a node may be to be worth
recording, and on how many nodes are recorded in total. All three are deliberately
**shape-agnostic** — none may depend on which path through the tree happened to be
drawn first. See [`markCovered`](#markCovered) and [`maxDepth`](#maxDepth).

-}

import Dict exposing (Dict)
import Random
import RandomRun exposing (RandomRun)
import Set exposing (Set)


type Occupancy
    = {- Partly covered, and worth tracking. The set of covered children is
         maintained as we go rather than derived on demand: it's read on every
         draw, and folding the whole child dict each time makes a wide node cost
         O(width) per draw.
      -}
      Partial Int (Dict Int Occupancy) (Set Int)
    | {- Not worth tracking. Never exhausts, children never recorded. -} Open
    | {- Every input reachable from here has been tested. -} Covered


empty : Occupancy
empty =
    Partial 0 Dict.empty Set.empty


{-| Whether this part of the tree is untracked, so a draw need not consult it.
-}
isOpen : Occupancy -> Bool
isOpen occupancy =
    case occupancy of
        Open ->
            True

        _ ->
            False


isExhausted : Occupancy -> Bool
isExhausted occupancy =
    case occupancy of
        Covered ->
            True

        _ ->
            False


{-| The child values at this node that are fully covered, and so must not be
drawn again.

Empty for `Open` and for anything not yet visited, which is the common case —
that's what keeps the cost near zero until coverage actually happens.

-}
exhaustedChildren : Occupancy -> Set Int
exhaustedChildren occupancy =
    case occupancy of
        Partial _ _ covered ->
            covered

        Open ->
            Set.empty

        Covered ->
            Set.empty


{-| Descend to a child, so a draw can carry its position in the tree along with
it instead of walking from the root every time.
-}
childOf : Int -> Int -> Occupancy -> Occupancy
childOf value maxValue occupancy =
    case occupancy of
        Partial _ children _ ->
            case Dict.get value children of
                Just child ->
                    child

                Nothing ->
                    {- Transient: never stored, and has no covered children, so it
                       declines nothing. `markCovered` makes the real decision.
                    -}
                    Partial maxValue Dict.empty Set.empty

        Open ->
            Open

        Covered ->
            Covered


{-| Record that the input described by this run has been tested, and report how
much of the node budget is left.

`maxes` carries the branching factor at each position, which is what lets a node
know when all of its children are accounted for and it can collapse to `Covered`.

-}
markCovered : Int -> RandomRun -> List Int -> Occupancy -> Occupancy
markCovered runs run maxes occupancy =
    case markCoveredHelp runs maxDepth 0 run maxes occupancy of
        Nothing ->
            -- Unchanged, so hand back the same value rather than a copy.
            occupancy

        Just updated ->
            updated


{-| How far down a run coverage is recorded.

Without this the cost of recording a run grows with its length: `Fuzz.string` runs
are tens of draws long and `Fuzz.filter` multiplies that by its retries.

Shallow is enough for what this is for. The coverable parts of a fuzzer are near
the root -- `bool` is one draw, `pair bool bool` two, and the `Ok bool` branch of a
`oneOf` is two. Anything deeper is treated as never exhausting, which is the safe
direction: we decline nothing we shouldn't.

Three also replaces an explicit budget on tracked nodes. That budget existed to
bound products of narrow choices, but with nodes wider than
[`maxTrackedWidth`](#worthTracking) refused outright, depth alone bounds the
structure: at most `8 + 8^2 + 8^3` nodes, and in practice far fewer since nodes are
only created along runs that actually happen. Dropping the counter removes a tuple
allocated on every single run, which measured as a real cost for fuzzers whose runs
are cheap.

-}
maxDepth : Int
maxDepth =
    3


{-| `Nothing` means nothing changed.

This is what keeps the cost flat rather than growing with the number of runs. A
child that is already `Open` or `Covered` cannot change, so recursing into it and
then reinserting it would copy a path through the dictionary on every single run
for no reason -- and for a fuzzer that can never exhaust anything, _every_ run is
that case. Benchmarking put the whole mechanism at 0.16x of baseline on
`filter/even` with this missing, essentially all of it here.

-}
markCoveredHelp : Int -> Int -> Int -> RandomRun -> List Int -> Occupancy -> Maybe Occupancy
markCoveredHelp runs depthLeft index run maxes occupancy =
    case maxes of
        [] ->
            {- Out of bounds to walk. Two different situations, and they mean
               opposite things:

                 - the run ended here too, so this is a leaf and it's now covered;
                 - the run continues, which means recording stopped partway
                   because the draw entered an untracked region. Nothing to record.
            -}
            if index >= RandomRun.length run then
                case occupancy of
                    Covered ->
                        Nothing

                    _ ->
                        Just Covered

            else
                Nothing

        maxValue :: restOfMaxes ->
            case ( RandomRun.get index run, occupancy ) of
                ( Nothing, _ ) ->
                    -- Shouldn't happen: bounds are recorded alongside the run.
                    Nothing

                ( Just _, Open ) ->
                    Nothing

                ( Just _, Covered ) ->
                    Nothing

                ( Just value, Partial _ children covered ) ->
                    if depthLeft <= 0 then
                        -- Too deep to be worth recording.
                        Just Open

                    else if not (worthTracking runs (maxValue + 1)) then
                        {- Checked on the width of *this* node, not of the child
                           we're about to create. This node is the one that
                           accumulates a child per distinct value, so this is
                           where the cost lives. Testing the child instead left a
                           wide node recording a leaf for every value it saw,
                           which measured as a quarter of baseline throughput.
                        -}
                        Just Open

                    else
                        let
                            existing : Occupancy
                            existing =
                                case Dict.get value children of
                                    Just child ->
                                        child

                                    Nothing ->
                                        newChild runs restOfMaxes
                        in
                        case markCoveredHelp runs (depthLeft - 1) (index + 1) run restOfMaxes existing of
                            Nothing ->
                                -- Nothing below changed, so nothing here did.
                                Nothing

                            Just updatedChild ->
                                let
                                    updatedCovered : Set Int
                                    updatedCovered =
                                        if isExhausted updatedChild then
                                            Set.insert value covered

                                        else
                                            covered
                                in
                                if Set.size updatedCovered == maxValue + 1 then
                                    {- Collapsing keeps the structure small, and is
                                       what propagates coverage up to the root.
                                    -}
                                    Just Covered

                                else
                                    Just (Partial maxValue (Dict.insert value updatedChild children) updatedCovered)


{-| Whether a newly discovered node is worth tracking, and what that costs.

Two bounds, both shape-agnostic:

  - **Its own branching factor** has to be coverable within the run count. A
    `uniformInt 0 1000` node needs around `1001 * ln 1001` draws to fill, so
    tracking it means paying for a thousand runs and never collapsing.
  - **A budget on tracked nodes overall**, because branching factor alone says
    nothing about a _product_: `pair (intRange 0 30) (intRange 0 30)` is two
    perfectly narrow nodes with 961 leaves between them.

The obvious third measure — the size of the subtree below the node — is better
than either and unusable as a rule. The subtree below a choice depends on the
choice, so the answer changes with whichever run reaches the node first. For
`oneOf [ Err string, Ok bool ]` an `Err` run would mark the root untracked and
lose the `Ok` branch, which is the one case this mechanism exists for.

-}
newChild : Int -> List Int -> Occupancy
newChild runs restOfMaxes =
    case restOfMaxes of
        [] ->
            {- A leaf, created empty rather than already covered so that the step
               to `Covered` is a real change and propagates: reporting it covered
               on creation makes the parent see "nothing changed" and never add it
               to its covered set, so nothing ever collapses.
            -}
            Partial 0 Dict.empty Set.empty

        childMax :: _ ->
            if worthTracking runs (childMax + 1) then
                Partial childMax Dict.empty Set.empty

            else
                Open


{-| Whether a node this wide is worth keeping coverage records for.

Two conditions, and the second is the one that matters in practice.

_Coverable_: random draws repeat, so covering `n` distinct values takes about
`n * ln n` draws (the coupon collector's problem), not `n`. There is no point
tracking a node that cannot fill within the run count.

_Worth it_: recording coverage means updating a persistent tree, which allocates
along the path it copies. A fuzz run can be as cheap as a third of a microsecond,
and a dozen node allocations cost more than that -- so tracking only pays where
coverage completes almost immediately and the saving is then total.

That second condition is what the measurements insisted on. With only the
coupon-collector test, `pair (intRange 0 30) (intRange 0 30)` and
`intRange 0 100 |> filter ...` both qualify -- 961 and 101 values, both coverable
inside 1000 runs -- and both came out at around a fifth of baseline throughput,
while the domains that matter (`bool`, `order`, `oneOfValues`, and the small
branch of a `oneOf`) are all under eight values and gain 45-90x.

So the width limit is deliberately severe. It gives up mid-sized domains, which we
would otherwise be able to cover completely, in exchange for never making anything
slower.

-}
worthTracking : Int -> Int -> Bool
worthTracking runs size =
    {- `size < 1` is the sentinel a sparse draw records: its generator doesn't
       produce every value in range, so the set of children isn't knowable from the
       bound and the node must never be tracked or declared covered.
    -}
    size >= 1 && size * bitsNeeded size * trackingMargin <= runs


trackingMargin : Int
trackingMargin =
    8


{-| A node wider than this is not tracked. See [`worthTracking`](#worthTracking).
-}
maxTrackedWidth : Int
maxTrackedWidth =
    8


bitsNeeded : Int -> Int
bitsNeeded n =
    bitsNeededHelp n 1


bitsNeededHelp : Int -> Int -> Int
bitsNeededHelp n acc =
    if n <= 1 then
        acc

    else
        bitsNeededHelp ((n + 1) // 2) (acc + 1)


{-| A prefix of choices that has not been taken before, for the next test case to
start from.

Walks down from the root picking a value at each node, and stops the moment it
picks one that has never been taken — everything after that point is new, so the
fuzzer can be left to draw it freely. Covered children are skipped, so the walk
never descends into a part of the space that is finished.

This is the whole reason there is no per-draw conditioning: the work of avoiding
already-tested inputs happens once here, before generation, instead of at every
`rollDice`. It's the approach Hypothesis's `DataTree.generate_novel_prefix` takes.

Two consequences worth being explicit about:

  - **A domain of size `n` is covered in `n` runs, not `n * ln n`.** Nothing is
    ever tested twice, so there are no duplicates to wait out. That makes early
    termination optimal and lets [`worthTracking`](#worthTracking) admit much
    larger domains than it could when coverage relied on chance.
  - **Values differ from what the same seed produced before.** Picking a novel
    prefix means not picking what the generator would have. There is no way to
    have both; this trades seed stability for never repeating an input.

The pick is uniform over a node's uncovered children rather than drawn from that
node's generator, because the generator isn't recorded in the tree. For the nodes
that get tracked this is usually exactly right — `oneOf`, `oneOfValues` and
`intRange` are uniform — but it does flatten `weightedBool`, which is how
`Fuzz.list` decides whether to continue. Storing each node's generator (as
Hypothesis stores its constraints) would fix that.

-}
novelPrefix : Random.Seed -> Occupancy -> ( List Int, Random.Seed )
novelPrefix seed occupancy =
    novelPrefixHelp seed maxDepth occupancy []


novelPrefixHelp : Random.Seed -> Int -> Occupancy -> List Int -> ( List Int, Random.Seed )
novelPrefixHelp seed depthLeft occupancy reversedPrefix =
    case occupancy of
        Partial maxValue children covered ->
            if depthLeft <= 0 || Dict.isEmpty children || Set.size covered > maxValue then
                {- Nothing recorded at this node yet, so whatever the fuzzer draws
                   here is already novel and there is no reason to force anything.
                   That also keeps us away from the placeholder bound that `empty`
                   carries before the first draw is observed.
                -}
                ( List.reverse reversedPrefix, seed )

            else
                let
                    ( value, newSeed ) =
                        pickUncovered covered maxValue seed
                in
                case Dict.get value children of
                    Nothing ->
                        -- Never taken, so everything from here on is new.
                        ( List.reverse (value :: reversedPrefix), newSeed )

                    Just child ->
                        novelPrefixHelp newSeed (depthLeft - 1) child (value :: reversedPrefix)

        Open ->
            ( List.reverse reversedPrefix, seed )

        Covered ->
            -- The caller checks for an exhausted root before asking.
            ( List.reverse reversedPrefix, seed )


{-| Pick a child that isn't covered.

Rejection first, since with a mostly-uncovered node it succeeds immediately, then
an exact scan. Unlike the old per-draw conditioning this runs once per test case,
so the scan's `O(width)` is affordable — and it is only safe at all because a
tracked node is always `Dense`, so every value in range is one its generator could
produce.

-}
pickUncovered : Set Int -> Int -> Random.Seed -> ( Int, Random.Seed )
pickUncovered covered maxValue seed =
    if Set.isEmpty covered then
        Random.step (Random.int 0 maxValue) seed

    else
        pickUncoveredHelp covered maxValue seed 8


pickUncoveredHelp : Set Int -> Int -> Random.Seed -> Int -> ( Int, Random.Seed )
pickUncoveredHelp covered maxValue seed attemptsLeft =
    let
        ( value, newSeed ) =
            Random.step (Random.int 0 maxValue) seed
    in
    if not (Set.member value covered) then
        ( value, newSeed )

    else if attemptsLeft <= 0 then
        case List.filter (\v -> not (Set.member v covered)) (List.range 0 maxValue) of
            [] ->
                ( value, newSeed )

            remaining ->
                let
                    ( index, finalSeed ) =
                        Random.step (Random.int 0 (List.length remaining - 1)) newSeed
                in
                ( remaining |> List.drop index |> List.head |> Maybe.withDefault value
                , finalSeed
                )

    else
        pickUncoveredHelp covered maxValue newSeed (attemptsLeft - 1)
