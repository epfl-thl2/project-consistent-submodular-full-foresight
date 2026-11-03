module

public import ConsistentSubmodular.MainStatements
import ConsistentSubmodular.Deterministic.Basic.Paths
import ConsistentSubmodular.Deterministic.Basic.WindowBounds
import ConsistentSubmodular.Deterministic.Certificates.HalfMixtureCertificate
import ConsistentSubmodular.Deterministic.Certificates.WindowCertificates
import ConsistentSubmodular.Deterministic.Impossibility.GridStream
import ConsistentSubmodular.Deterministic.Reduction.CertificateReduction
import ConsistentSubmodular.Deterministic.Reduction.ExponentialTails
import ConsistentSubmodular.Randomized.Constants
import ConsistentSubmodular.Randomized.AdaptivityGap.ConsecutiveIntervals
import ConsistentSubmodular.Randomized.AdaptivityGap.ConsecutiveReduction
import ConsistentSubmodular.Randomized.AdaptivityGap.IntervalSelection
import ConsistentSubmodular.Randomized.Reduction.Checkpoints
import ConsistentSubmodular.Randomized.Impossibility.HardInstance

/-!
Proofs of the statements in `MainStatements.lean`, one theorem per statement,
with exactly the stated types. Each theorem is assembled from the results it
depends on in the paper. The supporting modules are private imports; only the
statements and these theorems are re-exported to clients of Lean's module
system.
-/

public section
namespace ConsistentSubmodular

/-! ## The tight randomized bound (Section 2 and Appendix A) -/

/-- Proposition 1 (Appendix A.1): `Ψ` has a unique root `ξ⋆ ∈ (1/2, 1)`. -/
theorem psiRoot : PsiRootGoal :=
  Chains.psiRoot

/-- Theorem 1 (Appendix A.2): the hard coverage instance of Section 2.1. -/
theorem randomizedUpper : RandomizedUpperGoal := by
  obtain ⟨u₁, h0, h1, hphi, hxi⟩ := Chains.exists_hardConstants
  exact HardInstance.randomizedUpper_of h0 h1 hphi hxi

/-- Remark 1 (Appendix A.2), from Theorem 1. -/
theorem randomizedUpperLimit : RandomizedUpperLimitGoal :=
  HardInstance.randomizedUpperLimit_of randomizedUpper

/-- Lemma 1 (Appendix A.3): from clairvoyant addition robustness to
consistency. -/
theorem additionRobustReduction : AdditionRobustReductionGoal :=
  Checkpoints.additionRobustReduction

/-- Lemma 5 (Appendix A.4): finite minimax duality. -/
theorem minimax : MinimaxGoal :=
  Minimax.minimax

/-- Lemma 2 (Appendix A.4): an adaptivity gap of at least `α` gives
`α`-addition-robust distributions. -/
theorem intervalSelectionReduction : IntervalSelectionReductionGoal :=
  IntervalSelection.intervalSelectionReduction

/-- Lemma 3 (Appendix A.5): the adaptivity gap is smallest on nonincreasing
consecutive intervals with the equalizing distribution. -/
theorem consecutiveIntervalReduction : ConsecutiveIntervalReductionGoal :=
  Shadow.consecutiveIntervalReduction

/-- Lemma 4 (Appendix A.6): nonincreasing consecutive intervals with the
equalizing distribution have adaptivity gap at least `ξ⋆`, with equality for
three intervals. -/
theorem consecutiveIntervalGap : ConsecutiveIntervalGapGoal :=
  Chains.consecutiveIntervalGap

/-- Theorem 2 (Appendix A.7). By Lemma 4 the adaptivity gap is at least `ξ⋆`
for nonincreasing consecutive intervals with the equalizing distribution, and
Lemma 3 extends this to every interval-selection instance. Lemma 2 with
`α = ξ⋆` then gives a `ξ⋆`-addition-robust distribution for every instance, and
Lemma 1 with `γ = min{ε/3, 1/16}` gives the algorithm. -/
theorem randomizedLower : RandomizedLowerGoal := by
  obtain ⟨hξ, hξ1, -⟩ := psiRoot
  have hgap : ∀ (N : ℕ) (I : IntervalInstance N), xiStar ≤ I.adaptivityGap :=
    consecutiveIntervalReduction xiStar (by linarith) hξ1.le consecutiveIntervalGap.1
  exact Checkpoints.randomizedLower_of additionRobustReduction (by linarith) hξ1.le
    (fun n W _ => intervalSelectionReduction xiStar (by linarith) hξ1.le hgap n W)

/-- Main Result 1: Theorems 2 and 1. -/
theorem randomizedTight : RandomizedTightGoal :=
  ⟨randomizedLower, randomizedUpperLimit⟩

/-! ## The tight deterministic bound (Section 3 and Appendix B) -/

/-- Lemma 6 (Appendix B.1.2): behavior of `3/4`-approximate trajectories on the
stream `Σ`. -/
theorem gridStreamCrossing : GridStreamCrossingGoal :=
  GridStream.gridStreamCrossing

/-- Theorem 3 (Section 3.1 and Appendix B.1): the stream `Σ` with `m = k`. -/
theorem deterministicUpper : DeterministicUpperGoal :=
  GridStream.deterministicUpper

/-- The impossibility of Main Result 2 for constant recourse, from Theorem 3. -/
theorem deterministicUpperLimit : DeterministicUpperLimitGoal :=
  GridStream.deterministicUpperLimit_of deterministicUpper

/-- Theorem 5 (Appendices B.2.3 and B.2.4): certificates with linearly many
segments for every window give a deterministic clairvoyant
`O(ε⁻³ log(1/ε))`-consistent algorithm at the same level up to `ε`. -/
theorem certificateReduction : CertificateReductionGoal :=
  Reduction.certificateReduction

/-- Theorem 6 (Appendix B.2.2): every window instance admits a
`(1/√2, 3)`-certificate. -/
theorem sqrtTwoCertificates : SqrtTwoCertificatesGoal :=
  Certificates.sqrtTwoCertificates

/-- Theorem 7: every window instance admits a `(3/4, m + 3)`-certificate. -/
theorem threeQuarterCertificates : ThreeQuarterCertificatesGoal :=
  Certificates.threeQuarterCertificates

/-- Theorem 4, from Theorems 5 and 7: Theorem 5 with `C = 3` applies to the
`(3/4, m + 3)`-certificates of Theorem 7, since `m + 3 ≤ 3 (m + 1)`. -/
theorem deterministicLower : DeterministicLowerGoal := by
  obtain ⟨K, hK⟩ := certificateReduction 3
  refine ⟨K, fun ε hε hε1 => ?_⟩
  obtain ⟨R, hRK, hR⟩ := hK ε hε hε1
  exact ⟨R, hRK, hR (3 / 4) (by norm_num) le_rfl fun n W _ =>
    (threeQuarterCertificates n W).map fun Z =>
      Z.mono (show W.lastStage + 3 ≤ 3 * (W.lastStage + 1) by omega)⟩

/-- Main Result 2: Theorems 4 and 3. -/
theorem deterministicTight : DeterministicTightGoal :=
  ⟨deterministicLower, deterministicUpperLimit⟩

/-- Lemma B.1 (Appendix B.2.1): window bounds. -/
theorem windowBounds : WindowBoundsGoal :=
  WindowBounds.windowBounds

/-- Lemma B.2 (Appendix B.2.1): mixture comparisons. -/
theorem mixtureComparisons : MixtureComparisonsGoal :=
  WindowBounds.mixtureComparisons

/-- Lemma B.3 (Appendix B.2.1): two-type interpolation. -/
theorem twoTypeInterpolation : TwoTypeInterpolationGoal :=
  WindowBounds.twoTypeInterpolation

/-- Theorem B.4 (Appendix B.2.2): the prefix–suffix tradeoff, which proves
Theorem 6 at `β = 1/√2`. -/
theorem prefixSuffixTradeoff : PrefixSuffixTradeoffGoal :=
  Certificates.prefixSuffixTradeoff

/-- Lemma B.5 (Appendix B.2.2): the prefix bound. -/
theorem prefixBound : PrefixBoundGoal :=
  Certificates.prefixBound

/-- Lemma B.6 (Appendix B.2.2): the suffix bound. -/
theorem suffixBound : SuffixBoundGoal :=
  Certificates.suffixBound

/-- Lemma B.7 (Appendix B.2.3): the concentration bounds. -/
theorem concentration : ConcentrationGoal :=
  Tails.concentration

end ConsistentSubmodular
