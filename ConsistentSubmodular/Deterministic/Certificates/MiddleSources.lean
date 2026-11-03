module

public import Mathlib

@[expose] public section

/-! Elementary source consequences for middle-parameter rollback. -/

namespace ConsistentSubmodular

theorem middle_child_elimination (q d p δ w P : ℝ) (hq4 : q ≤ 4)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P) :
    0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d := by
  have := mul_nonneg (sub_nonneg.mpr hq4) (sub_nonneg.mpr hper)
  rw [hatt] at *
  nlinarith only [this]

theorem middle_child_capacity (q d p δ w P : ℝ) (hq3 : q ≤ 3)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P)
    (hcap : w ≤ 1 - d - δ) :
    0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ := by
  have := mul_nonneg (sub_nonneg.mpr hq3) (sub_nonneg.mpr hcap)
  nlinarith only [this, hatt, hper]

theorem middle_child_credit_combination (q d p δ P : ℝ) (hq : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d)
    (hC : 0 ≤ q * (2 - 3 * d - P) - 3 * (1 - 4 * d)) :
    0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ := by
  have h1 := mul_nonneg hq hF
  have h2 := mul_nonneg (sub_nonneg.mpr hq3) hC
  nlinarith only [h1, h2]

theorem middle_child_delta_bound (q d p δ : ℝ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hd : 0 ≤ d) (hpd : d ≤ p)
    (hK : 0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : δ ≤ d := by
  have h1 := mul_nonneg (show 0 ≤ 3 - 2 * q by linarith) hK
  have hprod : 0 ≤ (3 - q) * ((5 - q) * d - (3 - q) * δ - (q + 1) * p) := by
    nlinarith only [h1, hJ]
  have hinner := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - q by linarith)
  have h2 := mul_nonneg (show 0 ≤ q + 1 by linarith) (sub_nonneg.mpr hpd)
  have h3 := mul_nonneg (sub_nonneg.mpr hq1) hd
  have hlast : 0 ≤ (3 - q) * (d - δ) := by nlinarith only [hinner, h2, h3]
  have := nonneg_of_mul_nonneg_right hlast (show 0 < 3 - q by linarith)
  linarith

theorem middle_child_deficit_first (q d p δ : ℝ)
    (_hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hpl : (19 : ℝ) / 80 ≤ p) (hpu : p ≤ 3 / 10)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 2 / 25 + 2 * p / 5 ≤ d := by
  have hcoef : 0 < 36 - 25 * q + 3 * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - 3 * q by linarith) (show 0 ≤ 7 - q by linarith)]
  have hlo : (36 - 25 * q + 3 * q ^ 2) * (7 / 40) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (19 / 80) ≤ 0 := by
    have := mul_nonneg_of_nonpos_of_nonpos (show 3 * q - 4 ≤ 0 by linarith)
      (show 11 * q - 18 ≤ 0 by linarith)
    nlinarith only [this]
  have hhi : (36 - 25 * q + 3 * q ^ 2) * (1 / 5) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (3 / 10) ≤ 0 := by
    nlinarith [sq_nonneg (q - 14 / 11)]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpu) hlo
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpl) hhi
  have hline : (36 - 25 * q + 3 * q ^ 2) * (2 / 25 + 2 * p / 5) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * p ≤ 0 := by
    nlinarith only [h1, h2]
  have hδterm := mul_nonneg (sq_nonneg q) hδ
  have hprod : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * (d - (2 / 25 + 2 * p / 5)) := by
    nlinarith only [hJ, hline, hδterm]
  have := nonneg_of_mul_nonneg_right hprod hcoef
  linarith

theorem middle_child_deficit_second (q d p δ : ℝ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hpl : (3 : ℝ) / 10 ≤ p) (hpu : p ≤ 1 / 2)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 1 / 8 + p / 4 ≤ d := by
  have hcoef : 0 < 36 - 25 * q + 3 * q ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - 3 * q by linarith) (show 0 ≤ 7 - q by linarith)]
  have hlo : (36 - 25 * q + 3 * q ^ 2) * (1 / 5) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (3 / 10) ≤ 0 := by
    nlinarith [sq_nonneg (q - 14 / 11)]
  have hhi : (36 - 25 * q + 3 * q ^ 2) * (1 / 4) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * (1 / 2) ≤ 0 := by
    have := mul_nonneg (show 0 ≤ q by linarith) (sub_nonneg.mpr hq1)
    nlinarith only [this]
  have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpu) hlo
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hpl) hhi
  have hline : (36 - 25 * q + 3 * q ^ 2) * (1 / 8 + p / 4) -
      (3 - q) * (3 - 2 * q) - q * (4 - q) * p ≤ 0 := by
    nlinarith only [h1, h2]
  have hδterm := mul_nonneg (sq_nonneg q) hδ
  have hprod : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * (d - (1 / 8 + p / 4)) := by
    nlinarith only [hJ, hline, hδterm]
  have := nonneg_of_mul_nonneg_right hprod hcoef
  linarith

theorem middle_parent_I (k d₀ d p W : ℝ) (hk4 : k ≤ 4)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hper : W + d₀ ≤ p) :
    0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀ := by
  have := mul_nonneg (sub_nonneg.mpr hk4) (sub_nonneg.mpr hper)
  nlinarith only [this, hatt]

theorem middle_parent_cutoff (k d₀ d p : ℝ)
    (_hk : (4 : ℝ) / 3 ≤ k) (_hk2 : k ≤ 2) (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4)
    (hpd : p ≤ 2 * d)
    (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀)
    (hfailed : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀) : (38 : ℝ) / 23 ≤ k := by
  by_cases hk9 : (9 : ℝ) / 5 ≤ k
  · linarith
  have h1 := mul_nonneg (show 0 ≤ 9 - 5 * k by linarith) (sub_nonneg.mpr hpd)
  have hupper : 0 ≤ 4 * k - 6 + (18 - 13 * k) * d := by
    nlinarith only [hI, hfailed, h1]
  by_cases hk18 : k ≤ 18 / 13
  · have h2 := mul_nonneg (show 0 ≤ 18 - 13 * k by linarith) (sub_nonneg.mpr hd4)
    nlinarith
  · have h2 := mul_nonneg (show 0 ≤ 13 * k - 18 by linarith) (sub_nonneg.mpr hd7)
    nlinarith

theorem middle_credit_V (k d₀ d p δ : ℝ)
    (hk : (3 : ℝ) / 2 ≤ k) (hk2 : k ≤ 2) (hd : 0 ≤ d) (hpd : p ≤ 2 * d)
    (hδ : δ ≤ d) (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀) :
    0 ≤ p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀ := by
  have h1 := mul_nonneg (sub_nonneg.mpr hk2) (show 0 ≤ 3 * d - p by linarith)
  have h2 := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) (sub_nonneg.mpr hδ)
  nlinarith only [hI, h1, h2]

theorem middle_child_benchmark_floor (q d p δ P : ℝ)
    (hq1 : 1 ≤ q) (hq3 : q < 3) (hd : 0 ≤ d) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hF : 0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d) :
    0 ≤ 2 * P - 3 * p - 4 * d - δ := by
  have hqδ := mul_nonneg (show 0 ≤ q by linarith) hδ
  have hprod : 0 ≤ (3 - q) * (P - p) := by nlinarith only [hF, hqδ, hd, hp]
  have hPp := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hq3)
  have h1 := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ P - p + δ by linarith)
  nlinarith only [hF, h1]

theorem middle_parent_p_floor (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd7 : (7 : ℝ) / 40 ≤ d) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀) : (49 : ℝ) / 200 ≤ p := by
  have h1 := mul_nonneg (show 0 ≤ 2 * (4 - k) by linarith) hd₀
  have h2 := mul_nonneg (show 0 ≤ k by linarith) (sub_nonneg.mpr hd7)
  have hprod : 0 ≤ (3 - k) * p := by nlinarith only [hI, h1, h2, hk]
  have hp := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  have h3 := mul_nonneg (sub_nonneg.mpr hk) hp
  nlinarith

end ConsistentSubmodular
