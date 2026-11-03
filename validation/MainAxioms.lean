module
import ConsistentSubmodular

/-! Check every exported proof against its statement, print the statements
and their definitions, and print the axioms of every exported proof.
The exported theorems are those of `comparator/config.json`. -/

example : ConsistentSubmodular.RandomizedTightGoal := ConsistentSubmodular.randomizedTight
example : ConsistentSubmodular.DeterministicTightGoal := ConsistentSubmodular.deterministicTight
example : ConsistentSubmodular.RandomizedUpperGoal := ConsistentSubmodular.randomizedUpper
example : ConsistentSubmodular.RandomizedUpperLimitGoal := ConsistentSubmodular.randomizedUpperLimit
example : ConsistentSubmodular.RandomizedLowerGoal := ConsistentSubmodular.randomizedLower
example : ConsistentSubmodular.AdditionRobustReductionGoal := ConsistentSubmodular.additionRobustReduction
example : ConsistentSubmodular.IntervalSelectionReductionGoal := ConsistentSubmodular.intervalSelectionReduction
example : ConsistentSubmodular.ConsecutiveIntervalReductionGoal := ConsistentSubmodular.consecutiveIntervalReduction
example : ConsistentSubmodular.ConsecutiveIntervalGapGoal := ConsistentSubmodular.consecutiveIntervalGap
example : ConsistentSubmodular.PsiRootGoal := ConsistentSubmodular.psiRoot
example : ConsistentSubmodular.MinimaxGoal := ConsistentSubmodular.minimax
example : ConsistentSubmodular.DeterministicUpperGoal := ConsistentSubmodular.deterministicUpper
example : ConsistentSubmodular.DeterministicUpperLimitGoal := ConsistentSubmodular.deterministicUpperLimit
example : ConsistentSubmodular.DeterministicLowerGoal := ConsistentSubmodular.deterministicLower
example : ConsistentSubmodular.CertificateReductionGoal := ConsistentSubmodular.certificateReduction
example : ConsistentSubmodular.SqrtTwoCertificatesGoal := ConsistentSubmodular.sqrtTwoCertificates
example : ConsistentSubmodular.ThreeQuarterCertificatesGoal := ConsistentSubmodular.threeQuarterCertificates
example : ConsistentSubmodular.GridStreamCrossingGoal := ConsistentSubmodular.gridStreamCrossing
example : ConsistentSubmodular.WindowBoundsGoal := ConsistentSubmodular.windowBounds
example : ConsistentSubmodular.MixtureComparisonsGoal := ConsistentSubmodular.mixtureComparisons
example : ConsistentSubmodular.TwoTypeInterpolationGoal := ConsistentSubmodular.twoTypeInterpolation
example : ConsistentSubmodular.PrefixSuffixTradeoffGoal := ConsistentSubmodular.prefixSuffixTradeoff
example : ConsistentSubmodular.PrefixBoundGoal := ConsistentSubmodular.prefixBound
example : ConsistentSubmodular.SuffixBoundGoal := ConsistentSubmodular.suffixBound
example : ConsistentSubmodular.ConcentrationGoal := ConsistentSubmodular.concentration

#print ConsistentSubmodular.Objective
#print ConsistentSubmodular.arrivedPrefix
#print ConsistentSubmodular.recourse
#print ConsistentSubmodular.FeasibleTrajectory
#print ConsistentSubmodular.RandomTrajectory
#print ConsistentSubmodular.RandomTrajectory.Feasible
#print ConsistentSubmodular.RandomTrajectory.expectation
#print ConsistentSubmodular.ConsistentGuarantee
#print ConsistentSubmodular.RandomizedGuarantee
#print ConsistentSubmodular.coverageValue
#print ConsistentSubmodular.independentExpectation
#print ConsistentSubmodular.psi
#print ConsistentSubmodular.xiStar
#print ConsistentSubmodular.phi
#print ConsistentSubmodular.RandomizedUpperGoal
#print ConsistentSubmodular.RandomizedUpperLimitGoal
#print ConsistentSubmodular.RandomizedLowerGoal
#print ConsistentSubmodular.Point
#print ConsistentSubmodular.IsSimplex
#print ConsistentSubmodular.WindowInstance
#print ConsistentSubmodular.WindowInstance.SingleArrivals
#print ConsistentSubmodular.WindowInstance.benchmark
#print ConsistentSubmodular.WindowInstance.IsAdditionRobust
#print ConsistentSubmodular.AdmitsAdditionRobust
#print ConsistentSubmodular.AdditionRobustReductionGoal
#print ConsistentSubmodular.WindowInstance.lpValue
#print ConsistentSubmodular.WindowInstance.payoff
#print ConsistentSubmodular.IntervalInstance
#print ConsistentSubmodular.IntervalInstance.value
#print ConsistentSubmodular.IntervalInstance.fixedValue
#print ConsistentSubmodular.IntervalInstance.adaptiveValue
#print ConsistentSubmodular.IntervalInstance.adaptivityGap
#print ConsistentSubmodular.IntervalInstance.IsNonincreasingConsecutive
#print ConsistentSubmodular.IntervalInstance.IsEqualizing
#print ConsistentSubmodular.IntervalSelectionReductionGoal
#print ConsistentSubmodular.ConsecutiveIntervalReductionGoal
#print ConsistentSubmodular.ConsecutiveIntervalGapGoal
#print ConsistentSubmodular.PsiRootGoal
#print ConsistentSubmodular.MinimaxGoal
#print ConsistentSubmodular.DeterministicUpperGoal
#print ConsistentSubmodular.DeterministicUpperLimitGoal
#print ConsistentSubmodular.DeterministicLowerGoal
#print ConsistentSubmodular.vertex
#print ConsistentSubmodular.mix
#print ConsistentSubmodular.PolygonalPath
#print ConsistentSubmodular.PolygonalPath.Along
#print ConsistentSubmodular.WindowInstance.mixtureValue
#print ConsistentSubmodular.WindowInstance.Certificate
#print ConsistentSubmodular.AdmitsCertificates
#print ConsistentSubmodular.AdmitsArrivalCertificates
#print ConsistentSubmodular.CertificateReductionGoal
#print ConsistentSubmodular.SqrtTwoCertificatesGoal
#print ConsistentSubmodular.ThreeQuarterCertificatesGoal
#print ConsistentSubmodular.gridStreamCover
#print ConsistentSubmodular.rowsHeld
#print ConsistentSubmodular.GridStreamCrossingGoal
#print ConsistentSubmodular.WindowInstance.arrivalValue
#print ConsistentSubmodular.WindowInstance.gain
#print ConsistentSubmodular.WindowInstance.bufferMixtureValue
#print ConsistentSubmodular.WindowInstance.physicalVector
#print ConsistentSubmodular.WindowInstance.multilinearExtension
#print ConsistentSubmodular.WindowBoundsGoal
#print ConsistentSubmodular.MixtureComparisonsGoal
#print ConsistentSubmodular.twoTypeValue
#print ConsistentSubmodular.TwoTypeInterpolationGoal
#print ConsistentSubmodular.WindowInstance.residual
#print ConsistentSubmodular.WindowInstance.credit
#print ConsistentSubmodular.PrefixSuffixTradeoffGoal
#print ConsistentSubmodular.PrefixBoundGoal
#print ConsistentSubmodular.SuffixBoundGoal
#print ConsistentSubmodular.ConcentrationGoal
#print ConsistentSubmodular.RandomizedTightGoal
#print ConsistentSubmodular.DeterministicTightGoal

#print axioms ConsistentSubmodular.randomizedTight
#print axioms ConsistentSubmodular.deterministicTight
#print axioms ConsistentSubmodular.randomizedUpper
#print axioms ConsistentSubmodular.randomizedUpperLimit
#print axioms ConsistentSubmodular.randomizedLower
#print axioms ConsistentSubmodular.additionRobustReduction
#print axioms ConsistentSubmodular.intervalSelectionReduction
#print axioms ConsistentSubmodular.consecutiveIntervalReduction
#print axioms ConsistentSubmodular.consecutiveIntervalGap
#print axioms ConsistentSubmodular.psiRoot
#print axioms ConsistentSubmodular.minimax
#print axioms ConsistentSubmodular.deterministicUpper
#print axioms ConsistentSubmodular.deterministicUpperLimit
#print axioms ConsistentSubmodular.deterministicLower
#print axioms ConsistentSubmodular.certificateReduction
#print axioms ConsistentSubmodular.sqrtTwoCertificates
#print axioms ConsistentSubmodular.threeQuarterCertificates
#print axioms ConsistentSubmodular.gridStreamCrossing
#print axioms ConsistentSubmodular.windowBounds
#print axioms ConsistentSubmodular.mixtureComparisons
#print axioms ConsistentSubmodular.twoTypeInterpolation
#print axioms ConsistentSubmodular.prefixSuffixTradeoff
#print axioms ConsistentSubmodular.prefixBound
#print axioms ConsistentSubmodular.suffixBound
#print axioms ConsistentSubmodular.concentration

-- Supporting results must stay outside the public module interface.
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.finiteCheckpoint
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.uniformRoundedFamilies
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.admitsCertificates_of_arrivals
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.sampleExpectation_lower_tail
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.reductionRecourse_rate
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Reduction.certificateReduction
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Certificates.sqrtTwoCertificates
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Certificates.threeQuarterCertificates
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Certificates.prefixSuffixTradeoff
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.WindowBounds.windowBounds
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Tails.concentration
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.GridStream.deterministicUpper
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Chains.exists_hardConstants
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Chains.consecutiveIntervalGap
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Shadow.consecutiveIntervalReduction
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Minimax.minimax
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Minimax.saddlePoint
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.IntervalSelection.candidates_of_gap
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.Checkpoints.additionRobustReduction
#guard_msgs (drop info) in
#check_failure ConsistentSubmodular.HardInstance.randomizedUpper_of
