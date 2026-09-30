module Test.Fuzz exposing (fuzzTest)

import DebugConfig
import Dict exposing (Dict)
import Exhaustive exposing (Frontier)
import Fuzz.Internal exposing (Fuzzer)
import GenResult exposing (GenResult(..))
import MicroDictExtra as Dict
import MicroListExtra as List
import PRNG
import Random
import RandomRun exposing (RandomRun)
import Simplify
import Test.Distribution exposing (DistributionReport(..))
import Test.Distribution.Internal exposing (Distribution(..), ExpectedDistribution(..))
import Test.Expectation exposing (Expectation(..), FailData, FuzzTestExpectation(..))
import Test.Internal exposing (Test, TestVariant(..), blankDescriptionFailure)
import Test.Runner.Failure exposing (InvalidReason(..), Reason(..))


{-| Reject always-failing tests because of bad names.
-}
fuzzTest : String -> Maybe Int -> Distribution a -> Fuzzer a -> (a -> Expectation) -> Test
fuzzTest untrimmedDesc maybeRuns distribution fuzzer getExpectation =
    let
        desc =
            String.trim untrimmedDesc
    in
    if String.isEmpty desc then
        blankDescriptionFailure

    else
        validatedFuzzTest desc fuzzer (Test.Internal.wrapWithTryCatch getExpectation) maybeRuns distribution
            |> ElmTestVariant__Labeled desc
            |> Test.Internal.wrapTestVariant


{-| Knowing that the fuzz test isn't obviously invalid, run the test and package up the results.
-}
validatedFuzzTest : String -> Fuzzer a -> (a -> Expectation) -> Maybe Int -> Distribution a -> Test
validatedFuzzTest desc fuzzer getExpectation maybeRuns distribution =
    ElmTestVariant__FuzzTest
        maybeRuns
        (\seed runs fuzzerInts ->
            let
                _ =
                    if DebugConfig.shouldLogFuzzTests then
                        Debug.log "running fuzz test" desc

                    else
                        desc

                { failure, distributionReport, runsElapsed } =
                    case tryReproduceFailureFromFuzzerInts fuzzer getExpectation fuzzerInts of
                        Just runResult ->
                            runResult

                        Nothing ->
                            fuzzLoop
                                { fuzzer = fuzzer
                                , testFn = getExpectation
                                , initialSeed = seed
                                , runsNeeded = runs
                                , distribution = distribution
                                , frontierCap = frontierCap
                                }
                                (initLoopState seed
                                    distribution
                                    (shouldEnumerate runs distribution fuzzer)
                                )
            in
            case failure of
                Nothing ->
                    FuzzTestPass distributionReport

                Just failure_ ->
                    FuzzTestFail
                        { given = failure_.given
                        , randomRun = failure_.randomRun
                        , description = failure_.failData.description
                        , reason = failure_.failData.reason
                        , distributionReport = distributionReport
                        , runsElapsed = runsElapsed
                        , rerunFailure =
                            \() ->
                                case Fuzz.Internal.generate (PRNG.hardcoded failure_.randomRun) fuzzer of
                                    Generated { value } ->
                                        getExpectation value
                                            |> (\_ -> ())

                                    Rejected _ ->
                                        ()
                        }
        )
        |> Test.Internal.wrapTestVariant


tryReproduceFailureFromFuzzerInts : Fuzzer a -> (a -> Expectation) -> List Int -> Maybe RunResult
tryReproduceFailureFromFuzzerInts fuzzer getExpectation fuzzerInts =
    if List.isEmpty fuzzerInts then
        -- No fuzzer ints were passed – continue with a regular fuzz run.
        Nothing

    else
        -- When a fuzz test fails, we expose the list of integers in the
        -- `RandomRun` that caused the failure (after shrinking) to the
        -- runner. The runner can then store those integers, and pass them
        -- when running the tests again. This way, a previous failure can
        -- be reproduced quickly (no need to go through many runs plus
        -- shrinking again).
        let
            randomRun =
                RandomRun.fromList fuzzerInts
        in
        case Fuzz.Internal.generate (PRNG.hardcoded randomRun) fuzzer of
            Generated { value } ->
                case getExpectation value of
                    Pass _ ->
                        -- The saved `RandomRun` now passes – continue with
                        -- a regular fuzz run.
                        Nothing

                    Fail { failData } ->
                        Just
                            { failure =
                                Just
                                    { given = Just <| Test.Internal.toString value
                                    , randomRun = randomRun
                                    , failData = failData
                                    }

                            -- In this mode we can't do a distribution report, because we ran just once.
                            , distributionReport = NoDistribution ()
                            , runsElapsed = 1
                            }

            Rejected _ ->
                -- If the code of the test has changed, a saved `RandomRun` might
                -- not be usable anymore. If so, just ignore it and start a regular run.
                Nothing


type alias Failure =
    { given : Maybe String
    , randomRun : RandomRun
    , failData : FailData
    }


type alias LoopConstants a =
    { fuzzer : Fuzzer a
    , testFn : a -> Expectation
    , initialSeed : Random.Seed
    , runsNeeded : Int
    , distribution : Distribution a

    {- Give up on enumerating once the frontier is this wide. A wide frontier
       means a wide tree, which means we were never going to finish it.
    -}
    , frontierCap : Int
    }


type alias LoopState =
    { runsElapsed : Int
    , distributionCount : Maybe (Dict (List String) Int)
    , nextPowerOfTwo : Int
    , failure : Maybe Failure
    , currentSeed : Random.Seed

    {- `Nothing` once we've stopped enumerating, either because the tree was
       exhausted or because it was too wide to bother with.
    -}
    , frontier : Maybe Frontier

    {- True once enumeration has covered the entire space of choices, so there is
       provably nothing left to test and the loop can stop early however large
       the requested run count was.
    -}
    , exhausted : Bool

    {- Whether any enumerated value was generated at all. If every one was
       rejected then the fuzzer really is invalid and we should say so, rather
       than silently passing a test that never ran.
    -}
    , anyGenerated : Bool
    }


{-| Enumeration gives up once the frontier is this wide.

Small on purpose. The point is to spend a negligible number of runs discovering
that a tree is too big, not to make a good attempt at a big one -- `Fuzz.list
Fuzz.int` exceeds this within a handful of nodes. The values it did test before
giving up are the smallest ones, which are worth testing anyway.

-}
frontierCap : Int
frontierCap =
    64


{-| The most nodes we'll generate while deciding whether to enumerate.

Bounded so the decision can never cost much. Trees larger than this are sampled
instead, which gives up the chance to _prove_ a property over a mid-sized domain
in exchange for never regressing: walking a 961-node tree currently costs about
four times what sampling 1000 values does, because the enumerator allocates lists
per node. Worth revisiting once that's cheaper.

-}
maxEnumerationNodes : Int
maxEnumerationNodes =
    64


{-| Decide up front whether to walk the fuzzer's choice tree or sample randomly.

Generates values without testing any of them, which is what makes this safe: for
any fuzzer we end up sampling, the values tested are exactly the ones we would
have tested before, so a fixed seed keeps its existing meaning. Deciding as we go
instead would have every fuzz test try the all-zeros input first -- and not only
the ones that benefit. `Fuzz.string`'s all-zeros run answers its first
"another character?" coin with "no", so a single-path size estimate says the tree
has two leaves, and we'd test `""` before discovering otherwise.

The cost is small because the size estimate rejects hopeless trees on the first
node: `Fuzz.int` is refused after one generation, `Fuzz.string` after two. Only
trees that really are small are walked all the way.

Two reasons to refuse outright:

  - A distribution check is a statistical statement about a random sample, and an
    enumeration isn't one. `weightedBool 0.9` has two possible runs, so
    enumerating it reports 50/50 where the fuzzer's real distribution is 90/10 --
    every percentage in the report would be wrong.
  - A tree bigger than the requested run count can't be finished, so walking it
    would be a slower way of testing fewer values.

-}
shouldEnumerate : Int -> Distribution a -> Fuzzer a -> Bool
shouldEnumerate runsNeeded distribution fuzzer =
    case distribution of
        NoDistributionNeeded ->
            planEnumeration runsNeeded
                fuzzer
                (min runsNeeded maxEnumerationNodes)
                Exhaustive.initialFrontier
                []

        _ ->
            False


{-| Walk the tree without testing anything, reporting whether it can be finished
within the node budget.
-}
planEnumeration : Int -> Fuzzer a -> Int -> Frontier -> List Int -> Bool
planEnumeration runsNeeded fuzzer nodesLeft frontier prefix =
    if nodesLeft <= 0 then
        False

    else
        let
            prng : PRNG.PRNG
            prng =
                Fuzz.Internal.generate
                    (PRNG.enumerating (RandomRun.fromList prefix))
                    fuzzer
                    |> GenResult.getPrng

            newFrontier : Frontier
            newFrontier =
                Exhaustive.enqueue
                    (Exhaustive.expansionsOf
                        (List.length prefix)
                        (PRNG.getRun prng)
                        (PRNG.getMaxes prng)
                    )
                    frontier
        in
        if
            Exhaustive.size newFrontier
                > frontierCap
                || Exhaustive.estimatedTreeSize (runsNeeded + 1) (PRNG.getMaxes prng)
                > runsNeeded
        then
            False

        else
            case Exhaustive.next newFrontier of
                Nothing ->
                    -- Frontier emptied: the whole tree fits in the budget.
                    True

                Just ( nextPrefix, rest ) ->
                    planEnumeration runsNeeded fuzzer (nodesLeft - 1) rest nextPrefix


initLoopState : Random.Seed -> Distribution a -> Bool -> LoopState
initLoopState initialSeed distribution enumerate =
    let
        initialDistributionCount : Maybe (Dict (List String) Int)
        initialDistributionCount =
            Test.Distribution.Internal.getDistributionLabels distribution
                |> Maybe.map
                    (\labels ->
                        List.foldl
                            (\( label, _ ) dict -> Dict.insert [ label ] 0 dict)
                            Dict.empty
                            labels
                    )
    in
    { runsElapsed = 0
    , distributionCount = initialDistributionCount
    , nextPowerOfTwo = 1
    , failure = Nothing
    , currentSeed = initialSeed
    , frontier =
        if enumerate then
            Just Exhaustive.initialFrontier

        else
            Nothing
    , exhausted = False
    , anyGenerated = False
    }


{-| Runs fuzz tests repeatedly and returns information about distribution and possible failure.

The loop algorithm is roughly:

    if any failure:
        end with failure

    else if not enough tests ran (elapsed < total):
        run `total - elapsed` tests (short-circuiting on failure)
        loop

    else if doesn't need distribution check:
        end with success

    else if all labels sufficiently covered:
        end with success

    else if any label not sufficiently covered:
        set failure
        end with failure

    else:
        run `2^nextPowerOfTwo` tests (short-circuiting on failure)
        increment `nextPowerOfTwo`
        loop

-}
fuzzLoop : LoopConstants a -> LoopState -> RunResult
fuzzLoop c state =
    case state.failure of
        Just failure ->
            -- If the test fails, it still is useful to report the distribution even if we didn't do the statistical check for ExpectDistribution.
            -- For this reason we try to create DistributionToReport even in case of ExpectDistribution.
            { distributionReport =
                case state.distributionCount of
                    Nothing ->
                        Fuzz.Internal.noDistribution

                    Just distributionCount ->
                        DistributionToReport
                            { distributionCount = includeCombinationsInBaseCounts distributionCount
                            , runsElapsed = state.runsElapsed
                            }
            , failure = Just failure
            , runsElapsed = state.runsElapsed
            }

        Nothing ->
            if state.exhausted && not state.anyGenerated then
                {- Enumeration covered the whole tree and every single node was
                   rejected, so the fuzzer can't produce a value at all. Passing
                   here would be reporting success for a test that never ran.
                -}
                { distributionReport = Fuzz.Internal.noDistribution
                , failure =
                    Just
                        { given = Nothing
                        , randomRun = RandomRun.empty
                        , failData =
                            { description = "Fuzzer could not generate any value"
                            , reason = Invalid InvalidFuzzer
                            }
                        }
                , runsElapsed = state.runsElapsed
                }

            else if state.exhausted then
                {- The property held for every input the fuzzer can produce.
                   There is nothing left to test, so honour that rather than the
                   requested run count.
                -}
                { distributionReport = Fuzz.Internal.noDistribution
                , failure = Nothing
                , runsElapsed = state.runsElapsed
                }

            else if state.runsElapsed < c.runsNeeded then
                let
                    newState : LoopState
                    newState =
                        runNTimes (c.runsNeeded - state.runsElapsed) c state
                in
                fuzzLoop c newState

            else
                case c.distribution of
                    NoDistributionNeeded ->
                        { distributionReport = Fuzz.Internal.noDistribution
                        , failure = Nothing
                        , runsElapsed = state.runsElapsed
                        }

                    ReportDistribution _ ->
                        case state.distributionCount of
                            Nothing ->
                                -- Shouldn't happen, we're in the ReportDistribution case. This indicates a bug in `initLoopState`.
                                distributionBugRunResult

                            Just distributionCount ->
                                { distributionReport =
                                    DistributionToReport
                                        { distributionCount = includeCombinationsInBaseCounts distributionCount
                                        , runsElapsed = state.runsElapsed
                                        }
                                , failure = Nothing
                                , runsElapsed = state.runsElapsed
                                }

                    ExpectDistribution _ ->
                        let
                            normalizedDistributionCount : Maybe (Dict (List String) Int)
                            normalizedDistributionCount =
                                Maybe.map includeCombinationsInBaseCounts state.distributionCount
                        in
                        if allSufficientlyCovered c state normalizedDistributionCount then
                            {- Success! Well, almost. Now we need to check the Zero and MoreThanZero cases.

                               Unfortunately I don't see a good way of using the statistical test for this,
                               so we'll just hope the amount of tests we've done so far suffices.
                            -}
                            case findBadZeroRelatedCase c state normalizedDistributionCount of
                                Nothing ->
                                    case normalizedDistributionCount of
                                        Nothing ->
                                            -- Shouldn't happen, we're in the ReportDistribution case. This indicates a bug in `initLoopState`.
                                            distributionBugRunResult

                                        Just distributionCount ->
                                            { distributionReport =
                                                DistributionCheckSucceeded
                                                    { distributionCount = distributionCount
                                                    , runsElapsed = state.runsElapsed
                                                    }
                                            , failure = Nothing
                                            , runsElapsed = state.runsElapsed
                                            }

                                Just failedLabel ->
                                    distributionFailRunResult normalizedDistributionCount failedLabel

                        else
                            case findInsufficientlyCoveredLabel c state normalizedDistributionCount of
                                Nothing ->
                                    let
                                        newState : LoopState
                                        newState =
                                            runNTimes (2 ^ state.nextPowerOfTwo) c state
                                    in
                                    fuzzLoop c
                                        { runsElapsed = newState.runsElapsed
                                        , distributionCount = newState.distributionCount
                                        , nextPowerOfTwo = newState.nextPowerOfTwo + 1
                                        , failure = newState.failure
                                        , currentSeed = newState.currentSeed
                                        , frontier = newState.frontier
                                        , exhausted = newState.exhausted
                                        , anyGenerated = newState.anyGenerated
                                        }

                                Just failedLabel ->
                                    distributionFailRunResult normalizedDistributionCount failedLabel


type alias DistributionFailure =
    { label : String
    , actualPercentage : Float
    , expectedDistribution : ExpectedDistribution
    , runsElapsed : Int
    }


allSufficientlyCovered : LoopConstants a -> LoopState -> Maybe (Dict (List String) Int) -> Bool
allSufficientlyCovered c state normalizedDistributionCount =
    case normalizedDistributionCount of
        Nothing ->
            False

        Just distributionCount ->
            case Test.Distribution.Internal.getExpectedDistributions c.distribution of
                Nothing ->
                    False

                Just expectedDistributions ->
                    -- Needs normalized distribution count:
                    Dict.foldr
                        (\labels count soFar ->
                            case labels of
                                [ onlyLabel ] ->
                                    soFar && isLabelSufficientlyCovered state.runsElapsed expectedDistributions onlyLabel count

                                _ ->
                                    soFar
                        )
                        True
                        distributionCount


isLabelSufficientlyCovered : Int -> Dict String ExpectedDistribution -> String -> Int -> Bool
isLabelSufficientlyCovered runsElapsed expectedDistributions labels count =
    case Dict.get labels expectedDistributions of
        Nothing ->
            -- `Nothing` means something went wrong. We're answering the question "are all labels sufficiently covered?" and so the way to fail here is `False`.
            False

        Just expectedDistribution ->
            case expectedDistribution of
                -- Zero and MoreThanZero will get checked in the Success case
                Zero ->
                    True

                MoreThanZero ->
                    True

                AtLeast n ->
                    Test.Distribution.Internal.sufficientlyCovered runsElapsed count (n / 100)


findBadZeroRelatedCase : LoopConstants a -> LoopState -> Maybe (Dict (List String) Int) -> Maybe DistributionFailure
findBadZeroRelatedCase c state normalizedDistributionCount =
    case normalizedDistributionCount of
        Nothing ->
            Nothing

        Just distributionCount ->
            case Test.Distribution.Internal.getExpectedDistributionsAsList c.distribution of
                Nothing ->
                    Nothing

                Just expectedDistributions ->
                    expectedDistributions
                        |> List.find
                            (\( expectedDistribution, label, _ ) ->
                                case expectedDistribution of
                                    Zero ->
                                        -- TODO short-circuit Zero sooner: as soon as we increment its counter, during runNTimes.
                                        Dict.get [ label ] distributionCount
                                            -- TODO it would be better if we returned a bug failure here instead of failing with a dummy value
                                            |> Maybe.withDefault 1
                                            |> (/=) 0

                                    MoreThanZero ->
                                        Dict.get [ label ] distributionCount
                                            -- TODO it would be better if we returned a bug failure here instead of failing with a dummy value
                                            |> Maybe.withDefault 0
                                            |> (==) 0

                                    AtLeast _ ->
                                        False
                            )
                        |> Maybe.andThen
                            (\( expectedDistribution, label, _ ) ->
                                Dict.get [ label ] distributionCount
                                    |> Maybe.map
                                        (\count ->
                                            { label = label
                                            , actualPercentage = toFloat count * 100 / toFloat state.runsElapsed
                                            , expectedDistribution = expectedDistribution
                                            , runsElapsed = state.runsElapsed
                                            }
                                        )
                            )


findInsufficientlyCoveredLabel : LoopConstants a -> LoopState -> Maybe (Dict (List String) Int) -> Maybe DistributionFailure
findInsufficientlyCoveredLabel c state normalizedDistributionCount =
    case normalizedDistributionCount of
        Nothing ->
            Nothing

        Just distributionCount ->
            case Test.Distribution.Internal.getExpectedDistributions c.distribution of
                Nothing ->
                    Nothing

                Just expectedDistributions ->
                    -- TODO loop ExpectedDistributions instead of looping the label combinations?
                    distributionCount
                        -- Needs normalized distribution count:
                        |> Dict.toList
                        |> List.findMap
                            (\( labels, count ) ->
                                case labels of
                                    [ onlyLabel ] ->
                                        case Dict.get onlyLabel expectedDistributions of
                                            Just Zero ->
                                                Nothing

                                            Just MoreThanZero ->
                                                Nothing

                                            Just ((AtLeast n) as expectedDistribution) ->
                                                if Test.Distribution.Internal.insufficientlyCovered state.runsElapsed count (n / 100) then
                                                    Just
                                                        { label = onlyLabel
                                                        , actualPercentage = toFloat count * 100 / toFloat state.runsElapsed
                                                        , expectedDistribution = expectedDistribution
                                                        , runsElapsed = state.runsElapsed
                                                        }

                                                else
                                                    Nothing

                                            Nothing ->
                                                Nothing

                                    _ ->
                                        Nothing
                            )


distributionFailRunResult : Maybe (Dict (List String) Int) -> DistributionFailure -> RunResult
distributionFailRunResult normalizedDistributionCount failedLabel =
    case normalizedDistributionCount of
        Nothing ->
            -- Shouldn't happen, we're in the ExpectDistribution case. This indicates a bug in `initLoopState`.
            distributionBugRunResult

        Just distributionCount ->
            { distributionReport =
                DistributionCheckFailed
                    { distributionCount = distributionCount
                    , runsElapsed = failedLabel.runsElapsed
                    , badLabel = failedLabel.label
                    , badLabelPercentage = failedLabel.actualPercentage
                    , expectedDistribution = Test.Distribution.Internal.expectedDistributionToString failedLabel.expectedDistribution
                    }
            , failure = Just <| distributionInsufficientFailure failedLabel
            , runsElapsed = failedLabel.runsElapsed
            }


distributionBugRunResult : RunResult
distributionBugRunResult =
    { distributionReport = Fuzz.Internal.noDistribution
    , failure =
        Just
            { given = Nothing
            , randomRun = RandomRun.empty
            , failData =
                { description = "elm-test distribution collection bug"
                , reason = Invalid DistributionBug
                }
            }
    , runsElapsed = 0
    }


distributionInsufficientFailure : DistributionFailure -> Failure
distributionInsufficientFailure failure =
    { given = Nothing
    , randomRun = RandomRun.empty
    , failData =
        { description =
            """Distribution of label "{LABEL}" was insufficient:
  expected:  {EXPECTED_PERCENTAGE}
  got:       {ACTUAL_PERCENTAGE}.

(Generated {RUNS} values.)"""
                |> String.replace "{LABEL}" failure.label
                |> String.replace "{EXPECTED_PERCENTAGE}" (formatExpectedDistribution failure.expectedDistribution)
                |> String.replace "{ACTUAL_PERCENTAGE}" (Test.Distribution.Internal.formatPct failure.actualPercentage)
                |> String.replace "{RUNS}" (String.fromInt failure.runsElapsed)
        , reason = Invalid DistributionInsufficient
        }
    }


{-| Short-circuits on failure.
-}
runNTimes : Int -> LoopConstants a -> LoopState -> LoopState
runNTimes times c state =
    if times <= 0 || state.failure /= Nothing || state.exhausted then
        {- Stopping on `exhausted` is what makes early termination actually save
           anything: without it the batch runs to completion and `fuzzLoop` only
           notices afterwards, by which point the work is done.
        -}
        state

    else
        runNTimes (times - 1) c (runOnce c state)


{-| Generate a fuzzed value, test it, record the simplified test failure if any
and optionally categorize the value.
-}
runOnce : LoopConstants a -> LoopState -> LoopState
runOnce c state =
    case state.frontier of
        Just frontier ->
            runOnceEnumerating c state frontier

        Nothing ->
            runOnceRandom c state


{-| Test the next value in the enumeration of the fuzzer's choice tree.

Falls back to random sampling for the rest of the test as soon as the tree looks
too wide to finish, and records `exhausted` if it finishes.

-}
runOnceEnumerating : LoopConstants a -> LoopState -> Frontier -> LoopState
runOnceEnumerating c state frontier =
    case Exhaustive.next frontier of
        Nothing ->
            {- Only reachable on the very first call, before anything has been
               generated: the frontier starts empty and the all-zeros run has no
               prefix. Afterwards an empty frontier means exhausted, which is
               handled below.
            -}
            runEnumeratedPrefix c state frontier []

        Just ( prefix, rest ) ->
            runEnumeratedPrefix c state rest prefix


runEnumeratedPrefix : LoopConstants a -> LoopState -> Frontier -> List Int -> LoopState
runEnumeratedPrefix c state frontier prefix =
    let
        genResult : GenResult a
        genResult =
            Fuzz.Internal.generate
                (PRNG.enumerating (RandomRun.fromList prefix))
                c.fuzzer

        prng : PRNG.PRNG
        prng =
            GenResult.getPrng genResult

        newFrontier : Frontier
        newFrontier =
            Exhaustive.enqueue
                (Exhaustive.expansionsOf
                    (List.length prefix)
                    (PRNG.getRun prng)
                    (PRNG.getMaxes prng)
                )
                frontier

        {- An empty frontier after expanding means every choice sequence has been
           generated: the property holds for the entire input domain, whatever
           the requested run count was.
        -}
        finished : Bool
        finished =
            Exhaustive.size newFrontier == 0

        keptFrontier : Maybe Frontier
        keptFrontier =
            if
                finished
                    || Exhaustive.size newFrontier
                    > c.frontierCap
                    || Exhaustive.estimatedTreeSize (c.runsNeeded + 1) (PRNG.getMaxes prng)
                    > c.runsNeeded
            then
                {- Two ways to give up. Frontier width catches trees that branch
                   in many places; estimated size catches a single draw with a
                   huge range, which is width 1 and would otherwise have us
                   enumerate `Fuzz.int` one value at a time.
                -}
                Nothing

            else
                Just newFrontier
    in
    case genResult of
        Rejected _ ->
            {- Prune rather than fail. Enumeration starts from the smallest
               choices, which is exactly where `Fuzz.filter` predicates reject,
               so treating a rejection as an invalid fuzzer would fail tests that
               are perfectly fine. If *every* node is rejected we say so, which
               `fuzzLoop` checks via `anyGenerated`.
            -}
            { state
                | frontier = keptFrontier
                , exhausted = finished
            }

        Generated { value } ->
            { state
                | failure =
                    case c.testFn value of
                        Pass _ ->
                            Nothing

                        Fail { failData } ->
                            Just <|
                                findSimplestFailure
                                    { getExpectation = c.testFn
                                    , fuzzer = c.fuzzer
                                    , randomRun = PRNG.getRun prng
                                    , value = value
                                    , failData = failData
                                    }
                , runsElapsed = state.runsElapsed + 1
                , frontier = keptFrontier
                , exhausted = finished
                , anyGenerated = True
            }


runOnceRandom : LoopConstants a -> LoopState -> LoopState
runOnceRandom c state =
    let
        genResult : GenResult a
        genResult =
            Fuzz.Internal.generate
                (PRNG.random state.currentSeed)
                c.fuzzer

        maybeNextSeed : Maybe Random.Seed
        maybeNextSeed =
            genResult
                |> GenResult.getPrng
                |> PRNG.getSeed

        nextSeed : Random.Seed
        nextSeed =
            case maybeNextSeed of
                Just seed ->
                    seed

                Nothing ->
                    stepSeed state.currentSeed

        ( maybeFailure, newDistributionCounter ) =
            case genResult of
                Rejected { reason } ->
                    ( Just
                        { given = Nothing
                        , randomRun = RandomRun.empty
                        , failData =
                            { description = reason
                            , reason = Invalid InvalidFuzzer
                            }
                        }
                    , state.distributionCount
                    )

                Generated { prng, value } ->
                    let
                        failure : Maybe Failure
                        failure =
                            case c.testFn value of
                                Pass _ ->
                                    Nothing

                                Fail { failData } ->
                                    Just <|
                                        findSimplestFailure
                                            { getExpectation = c.testFn
                                            , fuzzer = c.fuzzer
                                            , randomRun = PRNG.getRun prng
                                            , value = value
                                            , failData = failData
                                            }

                        distributionCounter : Maybe (Dict (List String) Int)
                        distributionCounter =
                            Maybe.map2
                                (\labels old ->
                                    let
                                        foundLabels : List String
                                        foundLabels =
                                            labels
                                                |> List.filterMap
                                                    (\( label, predicate ) ->
                                                        if predicate value then
                                                            Just label

                                                        else
                                                            Nothing
                                                    )
                                    in
                                    Dict.increment foundLabels old
                                )
                                (Test.Distribution.Internal.getDistributionLabels c.distribution)
                                state.distributionCount
                    in
                    ( failure, distributionCounter )
    in
    { failure = maybeFailure
    , distributionCount = newDistributionCounter
    , currentSeed = nextSeed
    , runsElapsed = state.runsElapsed + 1
    , nextPowerOfTwo = state.nextPowerOfTwo
    , frontier = state.frontier
    , exhausted = state.exhausted
    , anyGenerated = True
    }


includeCombinationsInBaseCounts : Dict (List String) Int -> Dict (List String) Int
includeCombinationsInBaseCounts distribution =
    distribution
        |> Dict.map
            (\labels count ->
                case labels of
                    [ single ] ->
                        Dict.foldr
                            (\k value sum ->
                                if List.hasMultipleItems k && List.member single k then
                                    value + sum

                                else
                                    sum
                            )
                            count
                            distribution

                    _ ->
                        count
            )


formatExpectedDistribution : ExpectedDistribution -> String
formatExpectedDistribution expected =
    case expected of
        Zero ->
            "exactly 0%"

        MoreThanZero ->
            "more than 0%"

        AtLeast n ->
            Test.Distribution.Internal.formatPct n


type alias RunResult =
    { distributionReport : DistributionReport
    , failure : Maybe Failure

    {- How many values the fuzzer generated. Note this can be *more* than the
       configured `runs`: an `ExpectDistribution` test keeps going until the
       statistical check settles.

       This is reported to runners for failures, where it says how much work it
       took to uncover the defect. `DistributionReport` carries the same number,
       but only for tests that asked for a distribution report.
    -}
    , runsElapsed : Int
    }


{-| Random.next is private ¯\_(ツ)\_/¯
-}
stepSeed : Random.Seed -> Random.Seed
stepSeed seed =
    seed
        |> Random.step (Random.int 0 0)
        |> Tuple.second


findSimplestFailure : Simplify.State a -> Failure
findSimplestFailure state =
    let
        ( simplestValue, randomRun, failData ) =
            Simplify.simplify state
    in
    { given = Just <| Test.Internal.toString simplestValue
    , randomRun = randomRun
    , failData = failData
    }
