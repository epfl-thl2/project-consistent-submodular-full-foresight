module

public import ConsistentSubmodular.Deterministic.Certificates.ConstructorTests
public import ConsistentSubmodular.Deterministic.Certificates.EligibilityThreshold
public import ConsistentSubmodular.Deterministic.Certificates.HighAnchor
public import ConsistentSubmodular.Deterministic.Certificates.SmallParent

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem attainer_suff_of_fourThirds (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : (4 : ℝ) / 3 ≤ q) (hq3 : q < 3)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 ≤ P.suffEligibility h q s := by
  have hl := P.strongCredit_baseline hP h hA hc
  have hb := P.persistence_credit h s hhs
  have hatt := P.attaining_equation h s q hd heq
  have hh := attaining_suff_eligible (3 * (1 - P.designated h))
    (P.designated h - P.designated s) (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith [P.designated_le_one hP h])
    (sub_nonneg.mpr (P.designated_antitone hP hhs)) (by linarith) hq hq3 hatt
  exact hh

theorem high_anchor_profile_eligible (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : 1 ≤ q) (hq2 : q ≤ 2)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 ≤ P.actualEligibility h q s := by
  have hl := P.strongCredit_baseline hP h (by linarith) hc
  have hb := P.persistence_credit h s hhs
  have hatt := P.attaining_equation h s q hd heq
  have hh := high_anchor_attainer_eligible q (P.benchmark h - 1)
    (1 - P.designated h) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s))
    hq hq2 (by linarith [P.designated_le_one hP h]) (by linarith)
    (by unfold benchmark; linarith)
    (sub_nonneg.mpr (P.designated_antitone hP hhs))
    (by unfold benchmark at *; linarith) hatt
  unfold actualEligibility
  nlinarith only [hh]

theorem threshold_profile_eligible (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hA : (1281 : ℝ) / 1600 ≤ P.designated h) (hc : P.StrongCredit h)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    0 < P.actualEligibility h q s := by
  have hb := P.persistence_credit h s hhs
  have hatt := P.attaining_equation h s q hd heq
  have hh := threshold_attainer_eligible q (P.benchmark h - 1)
    (1 - P.designated h) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s))
    hq hq1 (by linarith [P.designated_le_one hP h]) (by linarith)
    (by linarith [P.one_le_benchmark hP h]) hc
    (sub_nonneg.mpr (P.designated_antitone hP hhs))
    (by unfold benchmark at *; linarith) hatt
  unfold actualEligibility
  nlinarith only [hh]

theorem checkpoint_of_baseline_stop (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 < P.designated h)
    (access : AccessCertificate P h)
    (hL : 3 * (1 - P.designated h) ≤ P.baseline h)
    (hq1 : 1 ≤ P.rawEnvelope h) (hq3 : P.rawEnvelope h ≤ 3 / 2) :
    Nonempty (CheckpointCertificate P) := by
  classical
  let q := P.rawEnvelope h
  have hqpos : 0 < q := by dsimp [q]; linarith
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hqpos
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have hb := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hd heq
  have hscalar := baseline_stop_scalar (P.designated h) (3 * (1 - P.designated h))
    (P.designated h - P.designated s) (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith [P.designated_le_one hP h]) (by linarith)
    (sub_nonneg.mpr (P.designated_antitone hP hhs.le)) (by linarith) hq1 hq3 hatt
  have helig : 0 ≤ P.actualEligibility h q s :=
    P.suff_implies_actual h s q hscalar.1
  have henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t := by
    intro t ht ha
    exact P.rawEnvelope_valid hP h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ha⟩)
  rcases P.actual_test hP h access q hq1 (by dsimp [q]; linarith) henv with hyes | hno
  · exact hyes
  · have hf := hno s hhs (Finset.mem_filter.mp hs).2.2 helig
    have hc := hscalar.2
    nlinarith only [hf, hc]

end AtomicProfile

namespace RelayHistory

variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem child_threshold_of_small_parameter (H : RelayHistory P h) (hP : P.Canonical)
    (hk : H.parameter < 4 / 3) : (1281 : ℝ) / 1600 < P.designated h := by
  have hA := H.small_parameter_high_anchor hk
  have helig := P.high_anchor_profile_eligible hP H.parent h H.advances.le hA
    H.parent_credit H.parameter H.parameter_ge_one (by linarith) H.denominator H.attaining
  have hf := H.failed_actual (by linarith) h H.advances H.child_active helig
  have hb := P.persistence_credit H.parent h H.advances.le
  have hatt := P.attaining_equation H.parent h H.parameter H.denominator H.attaining
  have hh := small_parent_child_threshold (1 - P.designated H.parent)
    (P.benchmark H.parent - 1) (P.designated H.parent - P.designated h)
    (P.designated h - P.residual H.parent h)
    ((P.benchmark h - P.designated H.parent) - (P.designated h - P.residual H.parent h))
    H.parameter (by linarith [P.designated_le_one hP H.parent]) (by linarith)
    (by linarith [P.one_le_benchmark hP H.parent]) H.parent_credit
    H.parameter_ge_one hk.le (by unfold AtomicProfile.benchmark at *; linarith)
    hatt (by nlinarith only [hf])
  linarith

end RelayHistory
end ConsistentSubmodular
