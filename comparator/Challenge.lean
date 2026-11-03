import ConsistentSubmodular.MainStatements

/-!
# The challenge for Lean's comparator

Every statement of `ConsistentSubmodular/MainStatements.lean`, with its proof left
open. `scripts/comparator.py` asks comparator to check that the theorems of
the same names in `Solution.lean` prove exactly these statements, use only the
axioms `propext`, `Quot.sound`, and `Classical.choice`, and pass the Lean
kernel. The statements themselves, and every definition they use, are in
`MainStatements.lean`, which imports only Mathlib.
-/

namespace ConsistentSubmodular

/-! ## Main results (Section 1.2) -/

theorem randomizedTight : RandomizedTightGoal := sorry
theorem deterministicTight : DeterministicTightGoal := sorry

/-! ## The tight randomized bound (Section 2 and Appendix A) -/

theorem randomizedUpper : RandomizedUpperGoal := sorry               -- Theorem 1
theorem randomizedUpperLimit : RandomizedUpperLimitGoal := sorry     -- Remark 1
theorem randomizedLower : RandomizedLowerGoal := sorry               -- Theorem 2
theorem additionRobustReduction : AdditionRobustReductionGoal := sorry   -- Lemma 1
theorem intervalSelectionReduction : IntervalSelectionReductionGoal := sorry  -- Lemma 2
theorem consecutiveIntervalReduction : ConsecutiveIntervalReductionGoal := sorry  -- Lemma 3
theorem consecutiveIntervalGap : ConsecutiveIntervalGapGoal := sorry     -- Lemma 4
theorem psiRoot : PsiRootGoal := sorry                               -- Proposition 1
theorem minimax : MinimaxGoal := sorry                               -- Lemma 5

/-! ## The tight deterministic bound (Section 3 and Appendix B) -/

theorem deterministicUpper : DeterministicUpperGoal := sorry         -- Theorem 3
theorem deterministicUpperLimit : DeterministicUpperLimitGoal := sorry   -- Main Result 2
theorem deterministicLower : DeterministicLowerGoal := sorry         -- Theorem 4
theorem certificateReduction : CertificateReductionGoal := sorry     -- Theorem 5
theorem sqrtTwoCertificates : SqrtTwoCertificatesGoal := sorry       -- Theorem 6
theorem threeQuarterCertificates : ThreeQuarterCertificatesGoal := sorry  -- Theorem 7
theorem gridStreamCrossing : GridStreamCrossingGoal := sorry         -- Lemma 6
theorem windowBounds : WindowBoundsGoal := sorry                     -- Lemma B.1
theorem mixtureComparisons : MixtureComparisonsGoal := sorry         -- Lemma B.2
theorem twoTypeInterpolation : TwoTypeInterpolationGoal := sorry     -- Lemma B.3
theorem prefixSuffixTradeoff : PrefixSuffixTradeoffGoal := sorry     -- Theorem B.4
theorem prefixBound : PrefixBoundGoal := sorry                       -- Lemma B.5
theorem suffixBound : SuffixBoundGoal := sorry                       -- Lemma B.6
theorem concentration : ConcentrationGoal := sorry                   -- Lemma B.7

end ConsistentSubmodular
