module

public import ConsistentSubmodular.Deterministic.Reduction.RecourseBound
public import ConsistentSubmodular.Deterministic.Reduction.ArrivalEncoding

@[expose] public section

/-!
# Theorem 5: from clairvoyant certificates to consistency

The reduction of Section 3.2, proved as in Appendices B.2.3 and B.2.4 with the
accuracy `η = 1/N` for `N = ⌊20/ε⌋ + 200` (`accuracy ε`). Each window of the
protected clock is compressed to `3N + 2` retained stages, so a certificate for
the compressed window has a segment budget independent of the stream. A
compressed stage may add several arrivals; its certificate comes from the
single-arrival encoding. Shared-threshold rounding turns the certificate into
one integral anchor and two operation lists, and the protected schedule
interleaves them with uniform recourse. Thresholds are drawn from a finite law
built from the tested probabilities (`SharedThreshold`), so the path vertices
need not be rational, unlike in Appendix B.2.3.

The steps of the paper are proved in the following modules.

* Simultaneous deterministic rounding (Appendix B.2.3): the retained stages
  (`BaselineBins`, `FractionalWindow`, `ArrivalEncoding`); the finite tests, the
  Lipschitz bound (34), and the test count (35) (`TypeLipschitz`,
  `PathSubdivision`, `WindowCounts`, `WindowTransfer`); the forced elements of
  large marginal value, (36) (`ForcedSet`, `SamplingScale`); one threshold per
  element (`SharedThreshold`, `ResidualRounding`, `FiniteJointRounding`,
  `JointRounding`); the tails of Lemma B.7 and the failure bounds (39) and
  (40) (`ExponentialTails`, `RoundingBudget`); Markov's inequality and the
  deterministic choice of thresholds (`FiniteProbability`,
  `SamplingCardinality`); the protection of every intermediate set
  (`PhysicalIntersection`, `PhysicalOperationPath`, `OperationPath`,
  `ForcedPath`); the rounded window with the bounds (41) and (42)
  (`WindowSampling`, `WindowSamples`, `RoundedWindow`,
  `WindowOperationAssembly`, `RoundedWindowExistence`); and the rounded bridges
  (`Bridge`, `BridgeGrid`, `BridgeSmall`, `BridgeRounding`).
* The protected schedule and the recourse calculation (Appendix B.2.4): the
  thinning inequality (43) (`Thinning`, `StreamingComparison`); the parameters
  and the rolling buffer (`StreamingParameters`, `SchedulingBasics`,
  `BufferRecourse`); the transition intervals (44) and the protection (45) by
  the buffer (`ProtectedClock`); the local windows and (46) (`ClockWindows`,
  `ClockRounded`); joining two windows (`ProgramAssembly`, `GlobalSchedule`,
  `BlockSchedule`, `FamilyTransfer`, `UniformRoundedFamilies`,
  `UniformTransfer`); and the recourse rate (`RecourseBound`).
-/

noncomputable section
namespace ConsistentSubmodular

namespace Reduction

/-- Certificates at level `α` give an `(α - ε)`-approximation whose recourse
depends only on the accuracy and on the segment budget, not on `α`. -/
theorem guarantee_of_certificates (O : CertificateFamily) {ε : ℝ} {N : ℕ} (hN : 200 ≤ N)
    (hNε : 20 * ((1 : ℝ) / N) < ε) :
    ConsistentGuarantee O.level ε (reductionRecourse N (O.budget (3 * N + 1))) :=
  guarantee_of_uniform_programs hN O.level_le hNε
    (uniform_programs_of_rounded_families (uniformRoundedFamilies O N hN))

/-- Theorem 5 (reduction from consistency to clairvoyant certificates), with
consistency `O(ε⁻³ log(1/ε))`. For `ε ≥ 3/4` every level is at most the slack,
so no recourse is needed. -/
theorem certificateReduction : CertificateReductionGoal := by
  intro C
  refine ⟨reductionConstant C, fun ε hε hε1 => ?_⟩
  by_cases hεα : ε < 3 / 4
  · refine ⟨reductionRecourse (accuracy ε) ((C + 1) * (3 * accuracy ε + 2)),
      reductionRecourse_rate C hε hεα, ?_⟩
    intro α hα0 hα harrivals
    have hcert := admitsCertificates_of_arrivals harrivals
    let O : CertificateFamily := {
      level := α
      budget := fun m => (C + 1) * (m + 1)
      level_nonneg := hα0.le
      level_le := hα
      budget_pos := fun m => by positivity
      certificates := fun n W =>
        (hcert n W).map (fun Z => Z.mono (Nat.mul_le_mul_right _ (Nat.le_succ C))) }
    exact guarantee_of_certificates O (accuracy_ge ε) (accuracy_slack hε)
  · refine ⟨0, ?_, fun α _ hα _ => consistentGuarantee_of_le_slack (by linarith) 0⟩
    have hlog : 0 ≤ Real.log (1 / ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have hK := reductionConstant_nonneg C
    have hpow : 0 ≤ (1 / ε) ^ 3 := pow_nonneg (div_nonneg zero_le_one hε.le) 3
    push_cast
    positivity

end Reduction

end ConsistentSubmodular
