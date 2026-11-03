module

public import ConsistentSubmodular.Deterministic.Certificates.ScalarGeometry

@[expose] public section

/-! Denominator-free row inequalities of the actual constructor and of its
automatic tails. Eligibility is an overlap-ceiling test. -/

namespace ConsistentSubmodular

theorem overlap_coefficient_bounds (q : ℝ) (hq0 : 0 < q) (hq2 : q ≤ 2) :
    0 < q - q ^ 2 / 4 ∧ q - q ^ 2 / 4 ≤ 1 := by
  constructor
  · nlinarith [mul_pos hq0 (show 0 < 1 - q / 4 by linarith)]
  · nlinarith [sq_nonneg (q - 2)]

theorem actual_eligibility_of_suff (A q δ w : ℝ)
    (hr : 0 ≤ A - δ - w)
    (hsuff : 0 ≤ w - (q - 1) * δ - 3 * (1 - A)) :
    0 ≤ 4 * A - 3 - q * δ - (q - q ^ 2 / 4) * (A - δ - w) := by
  have hc : 0 ≤ 1 - (q - q ^ 2 / 4) := by
    nlinarith [sq_nonneg (q - 2)]
  have := mul_nonneg hc hr
  have hid := eligibility_gap_identity A δ w q
  linarith

/-- Safety of every point of an initial partial edge, not only its endpoint. -/
theorem actual_entry_segment (A δ r x : ℝ)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hx : x ≤ 1 / 2)
    (hend : (3 : ℝ) / 4 ≤ A - δ * x - r * x * (1 - x))
    (z : ℝ) (_hz : 0 ≤ z) (hzx : z ≤ x) :
    (3 : ℝ) / 4 ≤ A - δ * z - r * z * (1 - z) := by
  have h1 : 0 ≤ x - z := sub_nonneg.mpr hzx
  have h2 : 0 ≤ δ + r * (1 - x - z) := by
    apply add_nonneg hδ
    apply mul_nonneg hr
    linarith
  nlinarith [mul_nonneg h1 h2]

theorem actual_prefix_margin (A q L g u gc rc : ℝ)
    (helig : 0 ≤ 4 * A - 3 - q * (A - gc) - (q - q ^ 2 / 4) * rc)
    (henv : 0 ≤ q * ((A - g) + (g - u)) + (L + g - A) +
      3 * (1 - A) - 4 * (g - u)) :
    (3 : ℝ) / 4 * (L + g) ≤
      L + (1 - q / 4) * u + (q / 4) * gc -
        (q / 4) * (1 - q / 4) * rc := by
  nlinarith

/-- Minimizing the suffix expression over the partner residual. -/
theorem actual_suffix_min_crossing (q u y : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) :
    (3 - (q - q ^ 2 / 4)) * u ≤
      (4 - q) * u + (q - 1) * y - (q - q ^ 2 / 4) * min u y := by
  by_cases h : u ≤ y
  · rw [min_eq_left h]
    nlinarith [mul_nonneg (show 0 ≤ q - 1 by linarith) (sub_nonneg.mpr h)]
  · have h' : y ≤ u := le_of_not_ge h
    rw [min_eq_right h']
    have hm : 0 ≤ (q - q ^ 2 / 4) - (q - 1) := by
      nlinarith [sq_nonneg q]
    nlinarith [mul_nonneg hm (sub_nonneg.mpr h')]

/-- The credit threshold proves every suffix row after the last eligible one.
All comparisons are denominator-free, including both sides of the crossing. -/
theorem actual_suffix_credit (A B q m δ w v : ℝ)
    (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hm : m = q - q ^ 2 / 4)
    (hcredit : 2 * A * q - 3 * B ≤ q * v)
    (hnoelig : m * w ≤ (q - m) * δ + m * A - B)
    (hres : w ≤ A - δ) :
    0 ≤ (1 - m) * A + v + m * δ - (3 - m) * w := by
  have hq : 0 < q := by linarith
  obtain ⟨hm0, hm1⟩ := overlap_coefficient_bounds q hq hq2
  rw [← hm] at hm0 hm1
  have h3 : 0 ≤ 3 - m := by linarith
  have hcr : 0 ≤ q * v - 2 * A * q + 3 * B := by linarith
  by_cases hcross : q * δ ≤ B
  · have hid :
        q * m * ((1 - m) * A + v + m * δ - (3 - m) * w) =
          m * (q * v - 2 * A * q + 3 * B) +
          (q ^ 2 * (q - 1) / 4) * (B - q * δ) +
          q * (3 - m) * ((q - m) * δ + m * A - B - m * w) := by
      rw [hm]
      ring
    have h1 := mul_nonneg (le_of_lt hm0) hcr
    have h2 : 0 ≤ (q ^ 2 * (q - 1) / 4) * (B - q * δ) := by
      apply mul_nonneg
      · apply div_nonneg
        · exact mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hq1)
        · norm_num
      · exact sub_nonneg.mpr hcross
    have h3' := mul_nonneg (mul_nonneg (le_of_lt hq) h3)
      (sub_nonneg.mpr hnoelig)
    have hqm : 0 < q * m := mul_pos hq hm0
    nlinarith
  · have hid :
        q * ((1 - m) * A + v + m * δ - (3 - m) * w) =
          (q * v - 2 * A * q + 3 * B) + 3 * (q * δ - B) +
          q * (3 - m) * (A - δ - w) := by ring
    have h1 := mul_nonneg (mul_nonneg (le_of_lt hq) h3) (sub_nonneg.mpr hres)
    nlinarith

/-- For a positive envelope at most one, eligibility alone provides all
later actual row inequalities. -/
theorem actual_low_suffix (A B D q m δc wc vc δ w : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (hm : m = q - q ^ 2 / 4)
    (hD : D = A - B)
    (henv : 0 ≤ q * (δc + wc) + vc + D - 4 * wc)
    (helig : 0 ≤ B - q * δc - m * (A - δc - wc))
    (hnoelig : B - q * δ - m * (A - δ - w) ≤ 0) :
    0 ≤ (1 - m) * A + vc + m * δ - (4 - q - m) * w := by
  have hid :
      q * ((1 - m) * A + vc + m * δ - (4 - q - m) * w) =
        q * (q * (δc + wc) + vc + D - 4 * wc) +
        4 * (B - q * δc - m * (A - δc - wc)) -
        (4 - q) * (B - q * δ - m * (A - δ - w)) := by
    rw [hm, hD]
    ring
  have h1 := mul_nonneg (le_of_lt hq) henv
  have h2 := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 4 - q by linarith) hnoelig
  nlinarith

end ConsistentSubmodular
