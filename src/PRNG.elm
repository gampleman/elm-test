module PRNG exposing (PRNG(..), enumerating, getMaxes, getRun, getSeed, hardcoded, random)

{-| A way to draw values. There are two ways:

1.  Random: draw genuinely new random values using a Random.Seed. We remember
    drawn values on the side.

2.  Hardcoded: draw predefined values out of a recorded RandomRun. Handy
    when reproducing a failure. This can run out of values to draw, but that
    shouldn't happen during the normal execution.

3.  Enumerating: replay a prefix of choices, then draw the smallest possible
    value (zero) for everything after it, recording the upper bound of every
    draw as we go. Those bounds are what lets `Exhaustive` walk the whole space
    of choices: they say how many alternatives existed at each position, which
    is information the other two modes throw away.

-}

import Random
import RandomRun exposing (RandomRun)


type PRNG
    = -- PERF: optimized from record to custom type arguments to skip _Utils_update:
      Random RandomRun Random.Seed
    | Hardcoded {- wholeRun: -} RandomRun {- unusedPart: -} RandomRun
    | Enumerating {- unusedPrefix: -} RandomRun {- runSoFar: -} RandomRun {- maxesSoFar: -} RandomRun


random : Random.Seed -> PRNG
random seed =
    Random RandomRun.empty seed


hardcoded : RandomRun -> PRNG
hardcoded run =
    Hardcoded run run


{-| Start an enumerating draw that replays the given prefix of choices first.
-}
enumerating : RandomRun -> PRNG
enumerating prefix =
    Enumerating prefix RandomRun.empty RandomRun.empty


getRun : PRNG -> RandomRun
getRun prng =
    case prng of
        Random run _ ->
            run

        Hardcoded wholeRun _ ->
            wholeRun

        Enumerating _ runSoFar _ ->
            runSoFar


getSeed : PRNG -> Maybe Random.Seed
getSeed prng =
    case prng of
        Random _ seed ->
            Just seed

        Hardcoded _ _ ->
            Nothing

        Enumerating _ _ _ ->
            Nothing


{-| The upper bound of every draw made, in order. Only an enumerating draw
records these; the others have no use for them and return an empty run.
-}
getMaxes : PRNG -> RandomRun
getMaxes prng =
    case prng of
        Random _ _ ->
            RandomRun.empty

        Hardcoded _ _ ->
            RandomRun.empty

        Enumerating _ _ maxes ->
            maxes
