module

public import ConsistentSubmodular.Deterministic.Certificates.RelayScalar

@[expose] public section

/-! The boundary edge in the four-thirds actual-constructor descent. -/

noncomputable section

namespace ConsistentSubmodular

private theorem concave_quadratic_nonnegative (c e l u x : ℝ)
    (hlx : l ≤ x) (hxu : x ≤ u)
    (hl : 0 ≤ -3 * l ^ 2 + c * l + e)
    (hu : 0 ≤ -3 * u ^ 2 + c * u + e) :
    0 ≤ -3 * x ^ 2 + c * x + e := by
  by_cases hs : 0 ≤ c - 3 * (x + l)
  · nlinarith [mul_nonneg (sub_nonneg.mpr hlx) hs]
  · have hs' : 0 ≤ 3 * (x + u) - c := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hxu) hs']

def fourThirdsDiscriminant (p d : ℝ) : ℝ :=
  -3 * d ^ 2 + (2 * p - 1 / 4) * d + (-p ^ 2 + p / 2)

theorem fourThirdsDiscriminant_lower (p : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2) :
    0 ≤ fourThirdsDiscriminant p (p / 2) := by
  have := mul_nonneg hp (show 0 ≤ 1 - 2 * p by linarith)
  unfold fourThirdsDiscriminant
  nlinarith

theorem fourThirdsDiscriminant_small (p d : ℝ) (hp : 0 ≤ p) (hp3 : p ≤ 1 / 3)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p)) :
    0 ≤ fourThirdsDiscriminant p d := by
  apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
    (p / 2) (p * (1 - p)) d hdlow hcredit
  · have := fourThirdsDiscriminant_lower p hp (by linarith)
    unfold fourThirdsDiscriminant at this
    nlinarith only [this]
  · have hprod : 0 ≤ p * (2 * p - 1) ^ 2 * (1 - 3 * p) :=
      mul_nonneg (mul_nonneg hp (sq_nonneg _)) (by linarith)
    nlinarith only [hprod]

theorem fourThirdsDiscriminant_interior (p d : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p))
    (hleft : 0 < 5 / 4 - 7 * d + p) (hright : 0 < 15 / 8 - 16 * d + 5 * p) :
    0 ≤ fourThirdsDiscriminant p d := by
  by_cases hp3 : p ≤ 1 / 3
  · exact fourThirdsDiscriminant_small p d hp hp3 hdlow hcredit
  · have hp3' : (1 : ℝ) / 3 ≤ p := le_of_not_ge hp3
    by_cases hsplit : p ≤ 55 / 152
    · apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
        (p / 2) (15 / 128 + 5 * p / 16) d hdlow (by linarith)
      · have := fourThirdsDiscriminant_lower p hp hp2
        unfold fourThirdsDiscriminant at this
        nlinarith only [this]
      · have hprod := mul_nonneg (show 0 ≤ p - 7 / 24 by linarith)
          (show 0 ≤ 55 / 152 - p by linarith)
        nlinarith only [hprod]
    · apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
        (p / 2) (5 / 28 + p / 7) d hdlow (by linarith)
      · have := fourThirdsDiscriminant_lower p hp hp2
        unfold fourThirdsDiscriminant at this
        nlinarith only [this]
      · have hprod := mul_nonneg (show 0 ≤ 2 - 4 * p by linarith)
          (show 0 ≤ 152 * p - 55 by linarith)
        nlinarith only [hprod]

private theorem edge_nonnegative_of_discriminant (B e r z : ℝ)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hdisc : 0 ≤ 4 * B * r - (e + r) ^ 2) :
    0 ≤ B - e * z - r * z * (1 - z) := by
  by_cases hr0 : r = 0
  · subst r
    have he : e = 0 := by nlinarith [sq_nonneg e]
    simp [he, hB]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hid : 4 * r * (B - e * z - r * z * (1 - z)) =
        (2 * r * z - (e + r)) ^ 2 + 4 * B * r - (e + r) ^ 2 := by ring
    nlinarith [sq_nonneg (2 * r * z - (e + r))]

private theorem edge_nonnegative_on_unit (B e r : ℝ)
    (hB : 0 ≤ B) (hend : 0 ≤ B - e)
    (hdisc : 0 < e + r → 0 < r - e → 0 ≤ 4 * B * r - (e + r) ^ 2)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ B - e * z - r * z * (1 - z) := by
  by_cases hr : 0 ≤ r
  · by_cases hleft : 0 < e + r
    · by_cases hright : 0 < r - e
      · exact edge_nonnegative_of_discriminant B e r z hB hr (hdisc hleft hright)
      · have hfactor : 0 ≤ e - r * z := by
          have := mul_nonneg hr (sub_nonneg.mpr hz1)
          linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hz1) hfactor]
    · have hfactor : 0 ≤ -e - r + r * z := by
        have := mul_nonneg hr hz
        linarith
      nlinarith [mul_nonneg hz hfactor]
  · have h1 := mul_nonneg (sub_nonneg.mpr hz1) hB
    have h2 := mul_nonneg hz hend
    have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hr)
      (mul_nonneg hz (sub_nonneg.mpr hz1))
    nlinarith

def fourThirdsBaseDelta (p d : ℝ) : ℝ := -5 / 16 + (9 : ℝ) / 2 * d - 2 * p

def fourThirdsBaseOverlap (p d : ℝ) : ℝ := 25 / 16 - (23 : ℝ) / 2 * d + 3 * p

/-- The boundary edge is safe at the threshold parameter four thirds. Its
formal residuals need not themselves form a feasible atomic profile. -/
theorem fourThirds_base_boundary (p d z : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hd4 : d ≤ 1 / 4) (hcredit : d ≤ p * (1 - p))
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ 1 / 4 - d - fourThirdsBaseDelta p d * z -
      fourThirdsBaseOverlap p d * z * (1 - z) := by
  apply edge_nonnegative_on_unit (1 / 4 - d) (fourThirdsBaseDelta p d)
    (fourThirdsBaseOverlap p d) (by linarith) ?_ ?_ z hz hz1
  · unfold fourThirdsBaseDelta
    nlinarith [sq_nonneg (p - 7 / 22)]
  · intro hleft hright
    have hm := fourThirdsDiscriminant_interior p d hp hp2 hdlow hcredit
      (by unfold fourThirdsBaseDelta fourThirdsBaseOverlap at hleft; linarith)
      (by unfold fourThirdsBaseDelta fourThirdsBaseOverlap at hright; linarith)
    unfold fourThirdsBaseDelta fourThirdsBaseOverlap fourThirdsDiscriminant at *
    nlinarith only [hm]

theorem fourThirds_negative_discriminant (p d : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hcredit : d ≤ p * (1 - p))
    (hnegative : fourThirdsDiscriminant p d < 0) :
    (1 : ℝ) / 3 < p ∧ (8 * p + 1) / 20 < d := by
  have hp3 : (1 : ℝ) / 3 < p := by
    by_contra hn
    have := fourThirdsDiscriminant_small p d hp (le_of_not_gt hn) hdlow hcredit
    linarith
  refine ⟨hp3, ?_⟩
  by_contra hn
  have hdupper : d ≤ (8 * p + 1) / 20 := le_of_not_gt hn
  have hm : 0 ≤ fourThirdsDiscriminant p d := by
    apply concave_quadratic_nonnegative (2 * p - 1 / 4) (-p ^ 2 + p / 2)
      (p / 2) ((8 * p + 1) / 20) d hdlow hdupper
    · have := fourThirdsDiscriminant_lower p hp hp2
      unfold fourThirdsDiscriminant at this
      nlinarith only [this]
    · have hprod := mul_nonneg (show 0 ≤ 1 - 2 * p by linarith)
        (show 0 ≤ 17 * p - 1 by linarith)
      nlinarith only [hprod]
  linarith

def fourThirdsBoundaryWeight (p d q : ℝ) : ℝ :=
  2 * (1 - d) - 3 * (1 - 4 * d) / q - (p + d)

def fourThirdsBoundaryDelta (p d q : ℝ) : ℝ :=
  ((3 - q) * fourThirdsBoundaryWeight p d q - (p + d) - 3 * d) / q

def fourThirdsBoundaryOverlap (p d q : ℝ) : ℝ :=
  1 - d - fourThirdsBoundaryDelta p d q - fourThirdsBoundaryWeight p d q

def fourThirdsBoundaryMargin (p d q z : ℝ) : ℝ :=
  1 / 4 - d - fourThirdsBoundaryDelta p d q * z -
    fourThirdsBoundaryOverlap p d q * z * (1 - z)

def fourThirdsBoundaryPolynomial (p d q z : ℝ) : ℝ :=
  q ^ 2 * (1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2) +
    q * ((-3 + 12 * d) * z + (-6 + 13 * d + 4 * p) * z ^ 2) +
    (9 - 36 * d) * z ^ 2

theorem fourThirds_boundary_polynomial (p d q z : ℝ) (hq : q ≠ 0) :
    q ^ 2 * fourThirdsBoundaryMargin p d q z = fourThirdsBoundaryPolynomial p d q z := by
  unfold fourThirdsBoundaryMargin fourThirdsBoundaryOverlap fourThirdsBoundaryDelta
    fourThirdsBoundaryWeight fourThirdsBoundaryPolynomial
  field_simp
  ring

theorem fourThirds_boundary_discriminant_identity (p d q : ℝ) (hq : q ≠ 0) :
    q * ((1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
      (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2) =
      (4 / 3 : ℝ) * fourThirdsDiscriminant p d -
        (q - 4 / 3) * (p ^ 2 + 4 * p * d - 2 * p + d) := by
  unfold fourThirdsBoundaryOverlap fourThirdsBoundaryDelta
    fourThirdsBoundaryWeight fourThirdsDiscriminant
  field_simp
  ring

private theorem polynomial_nonnegative_unit (a b c z : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hend : 0 ≤ a + b + c) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ a + b * z + c * z ^ 2 := by
  by_cases hc : 0 ≤ c
  · positivity
  · have h1 := mul_nonneg (sub_nonneg.mpr hz1) ha
    have h2 := mul_nonneg hz hend
    have h3 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc)
      (mul_nonneg hz (sub_nonneg.mpr hz1))
    nlinarith

/-- The formal credit-boundary edge is safe for every parameter at least four
thirds, including formal negative residual values on the boundary. -/
theorem fourThirds_boundary_edge (p d q z : ℝ) (hp : 0 ≤ p) (hp2 : p ≤ 1 / 2)
    (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4) (hcredit : d ≤ p * (1 - p))
    (hq : (4 : ℝ) / 3 ≤ q) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ fourThirdsBoundaryMargin p d q z := by
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have hB : 0 < 1 - 4 * d := by linarith
  have hcoef : p ^ 2 + 4 * p * d - 2 * p + d ≤ 0 := by
    have h1 := mul_nonneg (show 0 ≤ 4 * p + 1 by linarith)
      (sub_nonneg.mpr hcredit)
    have h2 := mul_nonneg hp (sq_nonneg (2 * p - 1))
    nlinarith only [h1, h2]
  by_cases hm : 0 ≤ fourThirdsDiscriminant p d
  · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hq) hcoef
    have hdisc : 0 ≤ (1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
        (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2 := by
      have hid := fourThirds_boundary_discriminant_identity p d q hq0
      have hqdisc : 0 ≤ q * ((1 - 4 * d) * fourThirdsBoundaryOverlap p d q -
          (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q) ^ 2) := by
        nlinarith only [hid, hm, h1]
      exact nonneg_of_mul_nonneg_right hqdisc hqpos
    have hr : 0 ≤ fourThirdsBoundaryOverlap p d q := by
      have hprod : 0 ≤ (1 - 4 * d) * fourThirdsBoundaryOverlap p d q := by
        nlinarith [sq_nonneg (fourThirdsBoundaryDelta p d q + fourThirdsBoundaryOverlap p d q)]
      exact nonneg_of_mul_nonneg_right hprod hB
    apply edge_nonnegative_of_discriminant _ _ _ _ (by linarith) hr
    nlinarith only [hdisc]
  · have hm' : fourThirdsDiscriminant p d < 0 := lt_of_not_ge hm
    obtain ⟨hp3, hd0⟩ := fourThirds_negative_discriminant p d hp hp2 hdlow hcredit hm'
    have hderiv : 0 ≤ (2 - 8 * d) + (20 * d - 8 * p - 1) * z +
        (31 * d + 12 * p - 10) * z ^ 2 := by
      apply polynomial_nonnegative_unit _ _ _ z (by linarith) (by linarith) ?_ hz hz1
      linarith
    have hAL : 0 ≤ 1 - p - 2 * d := by
      have := mul_nonneg (show 0 ≤ 1 - p by linarith) (show 0 ≤ 1 - 2 * p by linarith)
      nlinarith
    have hquadratic : 0 ≤ 1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2 := by
      have h1 := mul_nonneg hAL hz
      have h2 := mul_nonneg (show 0 ≤ 1 - d by linarith) (sq_nonneg z)
      linarith
    have hbase := fourThirds_base_boundary p d z hp hp2 hdlow hd4.le hcredit hz hz1
    have hproduct := mul_nonneg (sub_nonneg.mpr hq)
      (add_nonneg (div_nonneg hderiv (by norm_num : (0 : ℝ) ≤ 3))
        (mul_nonneg hquadratic (sub_nonneg.mpr hq)))
    have hid : fourThirdsBoundaryPolynomial p d q z =
        (16 / 9 : ℝ) * (1 / 4 - d - fourThirdsBaseDelta p d * z -
          fourThirdsBaseOverlap p d * z * (1 - z)) +
        (q - 4 / 3) *
          (((2 - 8 * d) + (20 * d - 8 * p - 1) * z +
              (31 * d + 12 * p - 10) * z ^ 2) / 3 +
            (1 / 4 - d + (1 - p - 2 * d) * z + (1 - d) * z ^ 2) * (q - 4 / 3)) := by
      unfold fourThirdsBoundaryPolynomial fourThirdsBaseDelta fourThirdsBaseOverlap
      ring
    have hpoly : 0 ≤ fourThirdsBoundaryPolynomial p d q z := by
      rw [hid]
      exact add_nonneg (mul_nonneg (by norm_num) hbase) hproduct
    rw [← fourThirds_boundary_polynomial p d q z hq0] at hpoly
    exact nonneg_of_mul_nonneg_right hpoly (sq_pos_of_pos hqpos)

/-- Returning from the safe formal boundary to a strictly failed source row.
The affine interpolation is performed in `(delta, baseline)` coordinates. -/
theorem fourThirds_low_baseline_relay (p d q δ w b z : ℝ)
    (hp : 0 < p) (hp2 : p ≤ 1 / 2) (hdlow : p / 2 ≤ d) (hd4 : d < 1 / 4)
    (hcredit : d ≤ p * (1 - p)) (hq : (4 : ℝ) / 3 ≤ q) (hq2 : q ≤ 2)
    (hδ : 0 ≤ δ) (hb : p + d ≤ b)
    (hratio : (3 - q) * w = q * δ + b + 3 * d)
    (hfail : b + w < 2 * (1 - d) - 3 * (1 - 4 * d) / q)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    0 < 1 / 4 - d - δ * z - (1 - d - δ - w) * z * (1 - z) := by
  let L := p + d
  let W := fourThirdsBoundaryWeight p d q
  let E := fourThirdsBoundaryDelta p d q
  let w₀ := (L + 3 * d) / (3 - q)
  let J₀ := 1 / 4 - d - (1 - d - w₀) * z * (1 - z)
  let Jstar := 1 / 4 - d - E * z - (1 - d - E - W) * z * (1 - z)
  let J := 1 / 4 - d - δ * z - (1 - d - δ - w) * z * (1 - z)
  have hqpos : 0 < q := by linarith
  have hq0 : q ≠ 0 := ne_of_gt hqpos
  have h3pos : 0 < 3 - q := by linarith
  have h30 : 3 - q ≠ 0 := ne_of_gt h3pos
  have hd : 0 ≤ d := by linarith
  have hL : 2 * d < L := by
    dsimp [L]
    nlinarith [sq_pos_of_pos hp]
  have hbL : 0 ≤ b - L := sub_nonneg.mpr hb
  have hstar : (3 - q) * W = q * E + L + 3 * d := by
    dsimp [E, fourThirdsBoundaryDelta, W, L]
    field_simp
    ring
  have hzero : (3 - q) * w₀ = L + 3 * d := by
    dsimp [w₀]
    field_simp
  have hfail' : b + w < W + L := by
    dsimp [W, fourThirdsBoundaryWeight, L]
    linarith
  have hδE : δ < E := by
    have h1 := mul_lt_mul_of_pos_left hfail' h3pos
    have h2 := mul_nonneg (show 0 ≤ 4 - q by linarith) hbL
    have hqδ : q * δ < q * E := by nlinarith only [h1, h2, hratio, hstar]
    by_contra hn
    have := mul_le_mul_of_nonneg_left (le_of_not_gt hn) hqpos.le
    linarith
  have hE : 0 < E := lt_of_le_of_lt hδ hδE
  have hw₀ : 3 * d < w₀ := by
    apply (lt_div_iff₀ h3pos).2
    have := mul_nonneg (sub_nonneg.mpr hq) hd
    nlinarith
  have hJ₀ : 0 < J₀ := by
    dsimp [J₀]
    by_cases ho : 0 ≤ 1 - d - w₀
    · have hquad := mul_le_mul_of_nonneg_left (quadratic_overlap_bound z) ho
      nlinarith
    · have hprod := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ho)
        (mul_nonneg hz (sub_nonneg.mpr hz1))
      nlinarith
  have hJstar : 0 ≤ Jstar :=
    fourThirds_boundary_edge p d q z hp.le hp2 hdlow hd4 hcredit hq hz hz1
  have hid : (3 - q) * E * J =
      (3 - q) * (E - δ) * J₀ + (3 - q) * δ * Jstar +
        E * (b - L) * z * (1 - z) := by
    dsimp [J, J₀, Jstar]
    linear_combination (E * z * (1 - z)) * hratio - (δ * z * (1 - z)) * hstar -
      ((E - δ) * z * (1 - z)) * hzero
  have hterm1 : 0 < (3 - q) * (E - δ) * J₀ :=
    mul_pos (mul_pos h3pos (sub_pos.mpr hδE)) hJ₀
  have hterm2 : 0 ≤ (3 - q) * δ * Jstar :=
    mul_nonneg (mul_nonneg h3pos.le hδ) hJstar
  have hterm3 : 0 ≤ E * (b - L) * z * (1 - z) :=
    mul_nonneg (mul_nonneg (mul_nonneg hE.le hbL) hz) (sub_nonneg.mpr hz1)
  have hpositive : 0 < ((3 - q) * E) * J := by linarith only [hid, hterm1, hterm2, hterm3]
  exact (mul_pos_iff_of_pos_left (mul_pos h3pos hE)).mp hpositive

end ConsistentSubmodular
