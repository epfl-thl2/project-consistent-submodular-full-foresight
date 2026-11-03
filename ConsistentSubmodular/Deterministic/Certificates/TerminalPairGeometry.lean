module

public import ConsistentSubmodular.Deterministic.Certificates.TerminalActualScalar

@[expose] public section

/-! Convex pair rounding and the terminal coordinate barrier, expressed as
finite scalar inequalities. -/

namespace ConsistentSubmodular

def pairPolynomial (L u v o x : ℝ) : ℝ := L + (1 - x) * u + x * v - x * (1 - x) * o

theorem pairPolynomial_mono_right (L u v o x z : ℝ) (ho : 0 ≤ o)
    (hderiv : 0 ≤ v - u - (1 - 2 * x) * o) (hxz : x ≤ z) :
    pairPolynomial L u v o x ≤ pairPolynomial L u v o z := by
  have h1 := mul_nonneg ho (sub_nonneg.mpr hxz)
  have h2 := mul_nonneg (sub_nonneg.mpr hxz) (add_nonneg hderiv h1)
  unfold pairPolynomial
  nlinarith only [h2]

theorem pairPolynomial_coordinate_upper (L G u v o z : ℝ)
    (huG : u ≤ G) (hoverlap : u + v - G ≤ o) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    pairPolynomial L u v o z ≤ L + (1 - z) * G + z ^ 2 * v := by
  have h1 := mul_nonneg hz (sub_nonneg.mpr hoverlap)
  have h2 := mul_nonneg (sub_nonneg.mpr hz') (sub_nonneg.mpr huG)
  have h3 : 0 ≤ G - u - z * (v - o) := by nlinarith only [h1, h2]
  have h4 := mul_nonneg (sub_nonneg.mpr hz') h3
  unfold pairPolynomial
  nlinarith only [h4]

/-- A good pair path moving toward an endpoint cannot cross the forbidden
terminal coordinate slice. Only pair inclusion-exclusion is needed. -/
theorem terminal_pair_endpoint_no_bad_minimum (L G u v o x : ℝ)
    (_hL : 0 ≤ L) (hG : 0 ≤ G) (_hv : 0 ≤ v) (hvG : v ≤ G) (huG : u ≤ G)
    (hoverlap : u + v - G ≤ o)
    (hno : ¬ (v * (L + G) < G ^ 2 ∧ G < 2 * v * x))
    (hsafe : ∀ z : ℝ, x ≤ z → z ≤ 1 →
      (3 : ℝ) / 4 * (L + G) ≤ pairPolynomial L u v o z) :
    ¬ (v * (L + G) < G ^ 2 ∧ G < 2 * v) := by
  rintro ⟨hmin, hbranch⟩
  have hvpos : 0 < v := by linarith
  have hden : 0 < 2 * v := by positivity
  have hxbound : 2 * v * x ≤ G := by
    by_contra hn
    exact hno ⟨hmin, lt_of_not_ge hn⟩
  let z := G / (2 * v)
  have hzx : x ≤ z := by
    apply (le_div_iff₀ hden).2
    nlinarith only [hxbound]
  have hz0 : 0 ≤ z := div_nonneg hG (le_of_lt hden)
  have hz1 : z ≤ 1 := by
    apply (div_le_one hden).2
    exact le_of_lt hbranch
  have hgood := (hsafe z hzx hz1).trans
    (pairPolynomial_coordinate_upper L G u v o z huG hoverlap hz0 hz1)
  have hzv : z * (2 * v) = G := div_mul_cancel₀ _ (ne_of_gt hden)
  have hid : 4 * v * (L + (1 - z) * G + z ^ 2 * v - (3 : ℝ) / 4 * (L + G)) =
      v * (L + G) - G ^ 2 := by
    dsimp [z]
    field_simp
    ring
  have hmul := mul_nonneg (show 0 ≤ 4 * v by positivity) (sub_nonneg.mpr hgood)
  rw [hid] at hmul
  linarith

end ConsistentSubmodular
