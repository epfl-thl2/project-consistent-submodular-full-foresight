module

public import ConsistentSubmodular.Deterministic.Certificates.SelectorState
public import ConsistentSubmodular.Deterministic.Certificates.HighAnchor
public import ConsistentSubmodular.Deterministic.Certificates.BaselineUpgrade

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace RelayHistory
variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem deficient_domain (H : RelayHistory P h) (hP : P.Canonical)
    (hhigh : (3 : ℝ) / 4 < P.designated h)
    (hdef : P.baseline h < 3 * (1 - P.designated h)) :
    (4 : ℝ) / 3 < H.parameter ∧ H.parameter < 2 ∧
      1 - P.designated H.parent < 1 / 8 ∧
      0 ≤ P.suffEligibility H.parent H.parameter h := by
  let k := H.parameter
  let d₀ := 1 - P.designated H.parent
  let e := P.designated H.parent - P.designated h
  let W := P.designated h - P.residual H.parent h
  let b := (P.benchmark h - P.designated H.parent) - W
  have hd : 0 ≤ d₀ := sub_nonneg.mpr (P.designated_le_one hP _)
  have he : 0 ≤ e := sub_nonneg.mpr (P.designated_antitone hP H.advances.le)
  have hchild : d₀ + e ≤ 1 / 4 := by dsimp [d₀, e]; linarith
  have hL := P.strongCredit_baseline hP H.parent H.parent_high.le H.parent_credit
  have hLb : P.baseline H.parent ≤ b := by
    have := P.persistence_credit H.parent h H.advances.le
    dsimp [b, W]; linarith
  have hatt : (3 - k) * W = k * e + b + 3 * d₀ :=
    P.attaining_equation H.parent h k H.denominator H.attaining
  have hbdef : b + W + e < 3 * (d₀ + e) := by
    dsimp [b, W, e, d₀, AtomicProfile.benchmark]
    linarith only [hdef]
  have hk2 : k < 2 := by
    by_contra hn
    have hh := relay_baseline_upgrade_high d₀ e W b k hd he
      ((P.baseline_nonnegative _).trans hLb) (le_of_not_gt hn) H.parameter_lt_three hatt
    linarith
  have hfailed : k * (b + W) < 2 * (1 - d₀) * k - 3 * (1 - 4 * d₀) := by
    have helig : 0 ≤ P.actualEligibility H.parent k h := by
      by_cases hk4 : (4 : ℝ) / 3 ≤ k
      · apply P.suff_implies_actual
        have := attaining_suff_eligible (3 * d₀) e W b k (by positivity) he
          (by dsimp [d₀] at *; linarith) hk4 H.parameter_lt_three hatt
        exact this
      · have hanchor := H.small_parameter_high_anchor (lt_of_not_ge hk4)
        have hp : d₀ ≤ P.benchmark H.parent - 1 := by
          dsimp [d₀, AtomicProfile.benchmark] at *
          linarith
        have hh := high_anchor_attainer_eligible k (P.benchmark H.parent - 1) d₀ e W b
          H.parameter_ge_one hk2.le hd (by dsimp [d₀]; linarith) hp he
          (by dsimp [d₀, AtomicProfile.benchmark] at *; linarith) hatt
        convert hh using 1
        dsimp [AtomicProfile.actualEligibility, d₀, e, W]
        ring
    have hh := H.failed_actual hk2.le h H.advances H.child_active helig
    dsimp [k, b, d₀] at *
    nlinarith only [hh]
  obtain ⟨hk4, hk2, hd8⟩ := deficient_child_parent_domain d₀ e W b
    (P.baseline H.parent) k hd he hchild hL hLb H.parameter_ge_one H.parameter_lt_three
    hatt hbdef hfailed
  refine ⟨hk4, hk2, hd8, ?_⟩
  exact attaining_suff_eligible (3 * d₀) e W b k (by positivity) he
    (by dsimp [d₀] at *; linarith) hk4.le H.parameter_lt_three hatt

end RelayHistory
end ConsistentSubmodular
