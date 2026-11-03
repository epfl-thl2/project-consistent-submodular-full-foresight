module

public import ConsistentSubmodular.Deterministic.Certificates.Access
public import ConsistentSubmodular.Deterministic.Certificates.FourThirdsBoundary

@[expose] public section

namespace ConsistentSubmodular

/-- The four-thirds relay combines its deficient-baseline boundary argument
with the general credit-to-determinant argument at larger baselines. -/
theorem fourThirds_strict_relay (d p δ w b q : ℝ)
    (hd : 0 ≤ d) (hd4 : d < 1 / 4) (_hp : 0 ≤ p)
    (hcredit : (1 : ℝ) / 2 ≤ p ∨ d ≤ p * (1 - p))
    (hδ : 0 ≤ δ) (hw : 0 ≤ w) (hr : δ + w ≤ 1 - d)
    (hden : 0 < δ + w) (hb : p + d ≤ b)
    (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hatt : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : q * (b + w) < 2 * (1 - d) * q - 3 * (1 - 4 * d)) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 <
      (1 - d) - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  have hqpos : 0 < q := by linarith
  by_cases hLD : 3 * d ≤ p + d
  · have hDw : 3 * d ≤ w := by
      have h1 := mul_nonneg (show 0 ≤ q - 1 by linarith) hw
      have h2 := mul_nonneg hqpos.le hδ
      nlinarith
    have hbupper : b ≤ 2 * (1 - d) - w := by
      by_contra hn
      have := mul_nonpos_of_nonneg_of_nonpos hqpos.le
        (show 2 * (1 - d) - b - w ≤ 0 by linarith)
      nlinarith
    have he := relayError_nonpos_of_baseline (1 - d) (3 * d) b w
      (by positivity) hDw (by linarith) (hLD.trans hb) hbupper
    have hm := credit_to_strict_determinant (1 - d) (3 * d) δ w b q hden
      (by nlinarith only [hatt]) (by nlinarith only [hfail]) he
    have hdisc : (δ + (1 - d - δ - w)) ^ 2 <
        (4 * (1 - d) - 3) * (1 - d - δ - w) := by nlinarith only [hm]
    have hr0 : 0 < 1 - d - δ - w := by
      have hrnonneg : 0 ≤ 1 - d - δ - w := by linarith
      nlinarith [sq_nonneg (δ + (1 - d - δ - w))]
    exact fun z _ _ => strict_edge_of_discriminant (1 - d) δ (1 - d - δ - w) hr0 hdisc z
  · have hc : d ≤ p * (1 - p) := by
      rcases hcredit with h | h
      · linarith
      · exact h
    have hp0 : 0 < p := by nlinarith [sq_nonneg p]
    have hp2 : p ≤ 1 / 2 := by linarith
    have hfail' : b + w < 2 * (1 - d) - 3 * (1 - 4 * d) / q := by
      have hid : q * (2 * (1 - d) - 3 * (1 - 4 * d) / q) =
          2 * (1 - d) * q - 3 * (1 - 4 * d) := by field_simp
      nlinarith
    intro z hz hz1
    have hs := fourThirds_low_baseline_relay p d q δ w b z hp0 hp2 (by linarith)
      hd4 hc hq hq2 hδ hb hatt hfail' hz hz1
    linarith

noncomputable section
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem strict_edge_child (hP : P.Canonical) (h s : Fin (m + 1)) (hhs : h ≤ s)
    (hstrict : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z)) :
    (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  refine ⟨?_, P.strongCredit_of_pessimisticEdge hP h s hhs (fun z hz hz1 => (hstrict z hz hz1).le)⟩
  have := hstrict 1 (by norm_num) (by norm_num)
  norm_num at this
  linarith

theorem fourThirds_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (3 : ℝ) / 4 < P.designated h) (hcredit : P.StrongCredit h)
    (q : ℝ) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    P.PessimisticSafeEdge h s ∧ (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  have hA1 := P.designated_le_one hP h
  have hδ := sub_nonneg.mpr (P.designated_antitone hP hhs.le)
  have hw := sub_nonneg.mpr (hP.2 s h)
  have hr := P.residual_nonnegative h s
  have hp := P.one_le_benchmark hP h
  have hper := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hden heq
  have hscalar := fourThirds_strict_relay (1 - P.designated h)
    (P.benchmark h - 1) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith) (by linarith) (by linarith) hcredit hδ hw (by linarith)
    (by linarith) (by unfold benchmark at *; linarith) hq hq2
    (by nlinarith only [hatt]) (by nlinarith only [hfail])
  have hstrict : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z) := by
    intro z hz hz1
    have := hscalar z hz hz1
    nlinarith only [this]
  exact ⟨fun z hz hz1 => (hstrict z hz hz1).le, P.strict_edge_child hP h s hhs.le hstrict⟩

theorem high_anchor_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) (hA1 : P.designated h < 1)
    (hcredit : P.StrongCredit h) (q : ℝ) (hq : 1 ≤ q)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    P.PessimisticSafeEdge h s ∧ (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  have hδ := sub_nonneg.mpr (P.designated_antitone hP hhs.le)
  have hw := sub_nonneg.mpr (hP.2 s h)
  have hr := P.residual_nonnegative h s
  have hp := P.one_le_benchmark hP h
  have hper := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hden heq
  have hscalar := high_anchor_strict_relay (1 - P.designated h)
    (P.benchmark h - 1) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith) (by linarith) (by linarith) hcredit hδ (by linarith)
    (by linarith) (by unfold benchmark at *; linarith) hq
    (by nlinarith only [hatt]) (by nlinarith only [hfail])
  have hstrict : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z) := by
    intro z _ _
    have := hscalar z
    nlinarith only [this]
  exact ⟨fun z hz hz1 => (hstrict z hz hz1).le, P.strict_edge_child hP h s hhs.le hstrict⟩

end AtomicProfile
end
end ConsistentSubmodular
