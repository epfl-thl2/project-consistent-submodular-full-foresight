module

public import ConsistentSubmodular.Deterministic.Certificates.Envelope

@[expose] public section

namespace ConsistentSubmodular

/-- Every attaining row is sufficient-eligible from four thirds onward, given
the baseline budget supplied by strong credit. -/
theorem attaining_suff_eligible (D δ w b q : ℝ)
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hb : 2 * D / 3 ≤ b)
    (hq : (4 : ℝ) / 3 ≤ q) (hq3 : q < 3)
    (hatt : (3 - q) * w = q * δ + b + D) :
    0 ≤ w - (q - 1) * δ - D := by
  have hcoef : 0 ≤ q ^ 2 - 3 * q + 3 := by
    nlinarith [sq_nonneg (q - 3 / 2)]
  have h1 := mul_nonneg hcoef hδ
  have h2 := mul_nonneg (show 0 ≤ q - 4 / 3 by linarith) hD
  have hid : (3 - q) * (w - (q - 1) * δ - D) =
      b - (2 - q) * D + (q ^ 2 - 3 * q + 3) * δ := by
    nlinarith only [hatt]
  nlinarith

/-- A baseline of at least the deficit budget supplies both eligibility and
the required credit for parameters between one and three halves. -/
theorem baseline_stop_scalar (A D δ w b q : ℝ)
    (hD : 0 ≤ D) (hDA : D ≤ A) (hδ : 0 ≤ δ) (hb : D ≤ b)
    (hq1 : 1 ≤ q) (hq3 : q ≤ 3 / 2)
    (hatt : (3 - q) * w = q * δ + b + D) :
    0 ≤ w - (q - 1) * δ - D ∧
      2 * A * q - 3 * (A - D) ≤ q * (b + w) := by
  have hq0 : 0 < q := by linarith
  have hden : 0 < 3 - q := by linarith
  have hcoef : 0 ≤ q ^ 2 - 3 * q + 3 := by
    nlinarith [sq_nonneg (q - 3 / 2)]
  have hsuff : 0 ≤ w - (q - 1) * δ - D := by
    have h1 := mul_nonneg hcoef hδ
    have h2 := mul_nonneg (sub_nonneg.mpr hq1) hD
    nlinarith
  refine ⟨hsuff, ?_⟩
  have hlow : 0 ≤ (3 - q) * (b + w) - (5 - q) * D := by
    have h1 := mul_nonneg hq0.le hδ
    have h2 := mul_nonneg (show 0 ≤ 4 - q by linarith) (sub_nonneg.mpr hb)
    nlinarith
  have hg : 0 ≤ (3 - 2 * q) * (3 - q) := by
    exact mul_nonneg (by linarith) hden.le
  have h1 := mul_nonneg (sub_nonneg.mpr hDA) hg
  have h2 := mul_nonneg hD (mul_nonneg hq0.le (sub_nonneg.mpr hq1))
  have h3 := mul_nonneg hq0.le hlow
  nlinarith

noncomputable section
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem persistence_credit (h t : Fin (m + 1)) (hht : h ≤ t) :
    P.baseline h + (P.designated t - P.residual h t) ≤
      P.benchmark t - P.designated h := by
  have hp := P.baseline_add_residual_monotone h hht
  change P.baseline h + P.designated h ≤ P.baseline t + P.residual h t at hp
  unfold benchmark
  linarith

theorem suff_implies_actual (h c : Fin (m + 1)) (q : ℝ)
    (hs : 0 ≤ P.suffEligibility h q c) : 0 ≤ P.actualEligibility h q c := by
  have hr := P.residual_nonnegative h c
  have ht := actual_eligibility_of_suff (P.designated h) q
    (P.designated h - P.designated c) (P.designated c - P.residual h c)
    (by linarith) hs
  unfold actualEligibility
  nlinarith only [ht]

theorem last_actual_partner (h s : Fin (m + 1)) (q : ℝ)
    (hs : s ∈ P.laterActive h) (he : 0 ≤ P.actualEligibility h q s) :
    ∃ c, c ∈ P.laterActive h ∧ s ≤ c ∧ 0 ≤ P.actualEligibility h q c ∧
      ∀ t, c < t → P.Active t → P.actualEligibility h q t < 0 := by
  classical
  let eligible := (P.laterActive h).filter (fun t => 0 ≤ P.actualEligibility h q t)
  have hne : eligible.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨hs, he⟩⟩
  let c := eligible.max' hne
  have hc : c ∈ eligible := Finset.max'_mem _ _
  have hcle := Finset.le_max' eligible s (Finset.mem_filter.mpr ⟨hs, he⟩)
  refine ⟨c, (Finset.mem_filter.mp hc).1, hcle, (Finset.mem_filter.mp hc).2, ?_⟩
  intro t hct ht
  by_contra hn
  have htelig : t ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, le_of_not_gt hn⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ t,
      lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2.1 hct, ht⟩
  exact (not_le_of_gt hct) (Finset.le_max' eligible t htelig)

end AtomicProfile
end
end ConsistentSubmodular
