module

public import ConsistentSubmodular.Deterministic.Certificates.AtomicFacts

@[expose] public section

/-! Target rows of low-parameter rollback. The later-row argument retains parent
cross-row persistence from the child attainer. -/

noncomputable section
namespace ConsistentSubmodular
namespace LowRollback

variable {m aCount : ℕ}

abbrev deficit (P : AtomicProfile m aCount) (t : Fin (m + 1)) : ℝ := 1 - P.designated t
abbrev shifted (P : AtomicProfile m aCount) (t : Fin (m + 1)) : ℝ := P.benchmark t - 1
abbrev gap (P : AtomicProfile m aCount) (i t : Fin (m + 1)) : ℝ :=
  P.designated t - P.residual i t

def Active (P : AtomicProfile m aCount) (t : Fin (m + 1)) : Prop :=
  P.baseline t < 3 * P.designated t

def ParentEligible (P : AtomicProfile m aCount) (a t : Fin (m + 1)) (k : ℝ) : Prop :=
  (k - 1) * deficit P t + (4 - k) * deficit P a ≤ gap P a t

def ceiling (k d₀ : ℝ) : ℝ := 2 - 3 / k + 3 * (4 - k) * d₀ / k

def U (k d₀ d p W : ℝ) : ℝ := d - 2 * ceiling k d₀ + 3 * p - (3 - k) * W
def V (k d₀ d p δ : ℝ) : ℝ := p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀
def VHigh (k d₀ d p δ : ℝ) : ℝ :=
  p - (k - 2) - (k - 1) * (3 - k) * (d + δ) - (4 - k) ^ 2 * d₀
def Y (k d₀ d p δ P : ℝ) : ℝ :=
  ((k - 1) * (3 - k) / k) * (P - (k - 1) * (d + δ) - (4 - k) * d₀)+
    ((k ^ 2 - 3 * k + 3) / k) * p - ceiling k d₀

def M₁ (k T Pt z u : ℝ) : ℝ := T + Pt - (3 - k) * z - k * u
def M₂ (k T Pt z u : ℝ) : ℝ := T + Pt - (4 - k) * z - (k - 1) * u

theorem gap_le_designated (P : AtomicProfile m aCount) (i t : Fin (m + 1)) :
    gap P i t ≤ P.designated t := sub_le_self _ (P.residual_nonnegative i t)

@[simp] theorem gap_self (P : AtomicProfile m aCount) (t : Fin (m + 1)) : gap P t t = 0 := sub_self _

theorem deficit_monotone (P : AtomicProfile m aCount) (hP : P.Canonical) :
    Monotone (deficit P) := by
  intro s t hst
  exact sub_le_sub_left (P.designated_antitone hP hst) 1

/-- Parent history remains available from every earlier row, not only from the
current carrier. This is the essential after-attainer source. -/
theorem cross_row_persistence (P : AtomicProfile m aCount) (i s t : Fin (m + 1))
    (hst : s ≤ t) : 0 ≤ shifted P t - shifted P s - gap P i t + gap P i s := by
  have hp := P.baseline_add_residual_monotone i hst
  unfold shifted gap AtomicProfile.benchmark
  linarith

theorem carrier_persistence (P : AtomicProfile m aCount) (h t : Fin (m + 1)) (hht : h ≤ t) :
    0 ≤ shifted P t - shifted P h - gap P h t := by
  have hp := cross_row_persistence P h h t hht
  rw [gap_self] at hp
  linarith

theorem eligible_margin (k d₀ d p W Δ Pt z u : ℝ)
    (hk0 : 0 ≤ k) (hk3 : k ≤ 3) (hΔ : 0 ≤ Δ)
    (hcredit : Pt ≤ ceiling k d₀) (hp : 0 ≤ Pt - p - u) (hW : 0 ≤ Pt - p - z + W) :
    U k d₀ d p W ≤ M₁ k (d + Δ) Pt z u := by
  have h1 := mul_nonneg (sub_nonneg.mpr hk3) hW
  have h2 := mul_nonneg hk0 hp
  unfold U M₁
  nlinarith

theorem before_low_margin (k d₀ d p δ Δ Pt z u : ℝ)
    (hk : 3 / 2 ≤ k) (hk2 : k ≤ 2) (hΔ : Δ ≤ δ)
    (hp : 0 ≤ Pt - p - u) (hcap : z ≤ (k - 1) * (d + Δ) + (4 - k) * d₀) :
    V k d₀ d p δ ≤ max (M₁ k (d + Δ) Pt z u) (M₂ k (d + Δ) Pt z u) := by
  have hbase : V k d₀ d p δ ≤ d + Δ + p - 2 * z := by
    have hc := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) (sub_nonneg.mpr hΔ)
    unfold V
    nlinarith
  by_cases hzu : u ≤ z
  · apply hbase.trans
    apply le_trans _ (le_max_left _ _)
    have hm := mul_nonneg (show 0 ≤ k - 1 by linarith) (sub_nonneg.mpr hzu)
    unfold M₁
    nlinarith
  · apply hbase.trans
    apply le_trans _ (le_max_right _ _)
    have hm := mul_nonneg (sub_nonneg.mpr hk2) (sub_nonneg.mpr (le_of_not_ge hzu))
    unfold M₂
    nlinarith

theorem before_high_margin (k d₀ d p δ Δ Pt z u : ℝ)
    (hk : 2 ≤ k) (hk3 : k ≤ 3) (hΔ : Δ ≤ δ)
    (hp : 0 ≤ Pt - p - u) (hres : u ≤ 1 - (d + Δ))
    (hcap : z ≤ (k - 1) * (d + Δ) + (4 - k) * d₀) :
    VHigh k d₀ d p δ ≤ M₂ k (d + Δ) Pt z u := by
  have h1 := mul_nonneg (show 0 ≤ k - 2 by linarith) (sub_nonneg.mpr hres)
  have h2 := mul_nonneg (show 0 ≤ 4 - k by linarith) (sub_nonneg.mpr hcap)
  have h3 := mul_nonneg (mul_nonneg (show 0 ≤ k - 1 by linarith) (sub_nonneg.mpr hk3))
    (sub_nonneg.mpr hΔ)
  unfold VHigh M₂
  nlinarith

/-- The after-attainer bound keeps the source term `Pt-P-z+zs ≥ 0` among its
hypotheses. -/
theorem after_margin (k d₀ d p δ P T Pt z u zs : ℝ)
    (hk : 3 / 2 < k) (hk3 : k < 3)
    (hs : zs ≤ (k - 1) * (d + δ) + (4 - k) * d₀)
    (ht : z ≤ (k - 1) * T + (4 - k) * d₀)
    (hchild : 0 ≤ Pt - p - u) (hres : 0 ≤ 1 - T - u)
    (hparent : 0 ≤ Pt - P - z + zs) :
    Y k d₀ d p δ P ≤ M₂ k T Pt z u := by
  have hk0 : 0 < k := by linarith
  have hL : 0 ≤ (k - 1) * (3 - k) := mul_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ k ^ 2 - 3 * k + 3 := by nlinarith [sq_nonneg (k - 3 / 2)]
  have h1 := mul_nonneg (show 0 ≤ (3 : ℝ) by norm_num) (sub_nonneg.mpr ht)
  have h2 := mul_nonneg hB hchild
  have h3 := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) hres
  have h4 := mul_nonneg hL hparent
  have h5 := mul_nonneg hL (sub_nonneg.mpr hs)
  have heq : k * (M₂ k T Pt z u - Y k d₀ d p δ P) =
      3 * ((k - 1) * T + (4 - k) * d₀ - z) + (k ^ 2 - 3 * k + 3) * (Pt - p - u)+
      (2 * k - 3) * (1 - T - u) + (k - 1) * (3 - k) * (Pt - P - z + zs)+
      (k - 1) * (3 - k) * ((k - 1) * (d + δ) + (4 - k) * d₀ - zs) := by
    unfold M₂ Y ceiling
    field_simp
    ring
  have hm : 0 ≤ k * (M₂ k T Pt z u - Y k d₀ d p δ P) := by rw [heq]; linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hk0).mp hm)

def suffRow (P : AtomicProfile m aCount) (a h t : Fin (m + 1)) (k : ℝ) : ℝ :=
  P.baseline t + (1 - k / 4) * P.residual a t + (k / 4) * P.residual h t-
    min (P.residual a t) (P.residual h t) / 4

theorem margin_one_suff_lower (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (_hah : a ≠ h) (k : ℝ) (_hk0 : 0 ≤ k) (_hk4 : k ≤ 4) :
    M₁ k (deficit P t) (shifted P t) (gap P a t) (gap P h t) ≤
      4 * (suffRow P a h t k - (3 : ℝ) / 4 * P.benchmark t) := by
  have hm := min_le_left (P.residual a t) (P.residual h t)
  unfold M₁ suffRow deficit shifted gap AtomicProfile.benchmark
  nlinarith

theorem margin_two_suff_lower (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (_hah : a ≠ h) (k : ℝ) (_hk0 : 0 ≤ k) (_hk4 : k ≤ 4) :
    M₂ k (deficit P t) (shifted P t) (gap P a t) (gap P h t) ≤
      4 * (suffRow P a h t k - (3 : ℝ) / 4 * P.benchmark t) := by
  have hm := min_le_right (P.residual a t) (P.residual h t)
  unfold M₂ suffRow deficit shifted gap AtomicProfile.benchmark
  nlinarith

theorem baseline_le_suffRow (P : AtomicProfile m aCount) (a h t : Fin (m + 1))
    (k : ℝ) (hk0 : 0 ≤ k) (hk4 : k ≤ 4) : P.baseline t ≤ suffRow P a h t k := by
  have hm : 0 ≤ min (P.residual a t) (P.residual h t) :=
    le_min (P.residual_nonnegative a t) (P.residual_nonnegative h t)
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (P.residual a t) (P.residual h t))
    (show 0 ≤ 1 - k / 4 by linarith)
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (P.residual a t) (P.residual h t))
    (show 0 ≤ k / 4 by positivity)
  unfold suffRow
  nlinarith

/-- Complete partition of all rows from the attaining parent child onward.
Eligible, before-attainer, and after-attainer rows are all covered; inactive
rows use their baseline. The original parent history is preserved. -/
theorem all_later_suff_of_credits (P : AtomicProfile m aCount) (hP : P.Canonical)
    (a h s : Fin (m + 1)) (hah : a ≠ h) (hhs : h ≤ s)
    (k : ℝ) (hk : 3 / 2 < k) (hk3 : k < 3)
    (hs : Active P s)
    (hsource : ceiling k (deficit P a) < shifted P s)
    (hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k (deficit P a))
    (hU : 0 ≤ U k (deficit P a) (deficit P h) (shifted P h) (gap P a h))
    (hV : k ≤ 2 → 0 ≤ V k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hVh : 2 ≤ k → 0 ≤ VHigh k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h))
    (hY : 0 ≤ Y k (deficit P a) (deficit P h) (shifted P h)
      (deficit P s - deficit P h) (shifted P s)) :
    ∀ t : Fin (m + 1), h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤
      suffRow P a h t k := by
  have hk0 : 0 ≤ k := by linarith
  have hk4 : k ≤ 4 := by linarith
  have hscap : gap P a s ≤ (k - 1) * deficit P s + (4 - k) * deficit P a := by
    have hn : ¬ ParentEligible P a s k := by
      intro he
      exact (not_le.mpr hsource) (hcredit s hhs hs he)
    exact le_of_lt (lt_of_not_ge hn)
  intro t hht
  by_cases hactive : Active P t
  · have h1 := margin_one_suff_lower P a h t hah k hk0 hk4
    have h2 := margin_two_suff_lower P a h t hah k hk0 hk4
    have hp := carrier_persistence P h t hht
    let Δ := deficit P t - deficit P h
    have hΔ : 0 ≤ Δ := sub_nonneg.mpr (deficit_monotone P hP hht)
    have hd : deficit P h + Δ = deficit P t := by dsimp [Δ]; ring
    by_cases he : ParentEligible P a t k
    · have hW := cross_row_persistence P a h t hht
      have hm := eligible_margin k (deficit P a) (deficit P h) (shifted P h)
        (gap P a h) Δ (shifted P t) (gap P a t) (gap P h t)
        hk0 hk3.le hΔ (hcredit t hht hactive he) hp hW
      rw [hd] at hm
      linarith
    · have hcap : gap P a t ≤ (k - 1) * (deficit P h + Δ) + (4 - k) * deficit P a := by
        rw [hd]
        exact le_of_lt (lt_of_not_ge he)
      by_cases hts : t ≤ s
      · have hδ : Δ ≤ deficit P s - deficit P h :=
          sub_le_sub_right (deficit_monotone P hP hts) _
        by_cases hk2 : k ≤ 2
        · have hm := before_low_margin k (deficit P a) (deficit P h) (shifted P h)
            (deficit P s - deficit P h) Δ (shifted P t) (gap P a t) (gap P h t)
            hk.le hk2 hδ hp hcap
          rw [hd] at hm
          have hg := hV hk2
          have hu := max_le h1 h2
          linarith
        · have hk2' : 2 ≤ k := le_of_not_ge hk2
          have hres : gap P h t ≤ 1 - (deficit P h + Δ) := by
            rw [hd]
            simpa only [deficit, sub_sub_cancel] using gap_le_designated P h t
          have hm := before_high_margin k (deficit P a) (deficit P h) (shifted P h)
            (deficit P s - deficit P h) Δ (shifted P t) (gap P a t) (gap P h t)
            hk2' hk3.le hδ hp hres hcap
          rw [hd] at hm
          have hg := hVh hk2'
          linarith
      · have hst : s ≤ t := le_of_not_ge hts
        have hparent := cross_row_persistence P a s t hst
        have hres : 0 ≤ 1 - deficit P t - gap P h t := by
          have hg := gap_le_designated P h t
          dsimp [deficit]
          linarith
        have hscap' : gap P a s ≤ (k - 1) * (deficit P h + (deficit P s - deficit P h))+
            (4 - k) * deficit P a := by simpa only [add_sub_cancel] using hscap
        have hm := after_margin k (deficit P a) (deficit P h) (shifted P h)
          (deficit P s - deficit P h) (shifted P s) (deficit P t) (shifted P t)
          (gap P a t) (gap P h t) (gap P a s) hk hk3 hscap'
          (by simpa only [hd] using hcap) hp hres hparent
        linarith
  · have hbase : (3 : ℝ) / 4 * P.benchmark t ≤ P.baseline t := by
      have hh : 3 * P.designated t ≤ P.baseline t := le_of_not_gt hactive
      unfold AtomicProfile.benchmark
      linarith
    exact hbase.trans (baseline_le_suffRow P a h t k hk0 hk4)

end LowRollback
end ConsistentSubmodular
