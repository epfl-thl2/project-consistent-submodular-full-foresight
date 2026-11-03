module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# The linear program of Section 2.1 and Appendix A.2

The scalar part of Theorem 1. For the weights `1`, `x`, and `y = x² (1 + x)`
the convex combination of the three approximation constraints uses `μ₀ = y`,
`μ₁ = y/x - y`, and `μ₂ = 1 - y/x`. It bounds the ratio by
`N / (1 + x + y - x y - y²/x)` with `N = 1 + x - y`, and the identity
`(1 + x + y - x y - y²/x) - N (1 + x y) = y Φ(x)` makes this bound
`1 / (1 + x y)` at the root `x = u₁` of `Φ`, where it is `ξ⋆`. `lp_bound` adds
the error terms of consistency and of the exact cardinality constraint.
-/

noncomputable section

namespace ConsistentSubmodular.HardInstance

/-- The weight `y = x² (1 + x)` of the third group; `u₂ = u₁² (1 + u₁)`. -/
def lpThird (x : ℝ) : ℝ := x ^ 2 * (1 + x)

/-- `μ₁ = y/x - y`. -/
def lpMuOne (x : ℝ) : ℝ := x * (1 + x) * (1 - x)

/-- `μ₂ = 1 - y/x`. -/
def lpMuTwo (x : ℝ) : ℝ := 1 - x * (1 + x)

/-- The numerator `N = 1 + x - y`. -/
def lpNumerator (x : ℝ) : ℝ := 1 + x - lpThird x

/-- The denominator `1 + x + y - x y - y²/x`, with `y²/x = x³ (1 + x)²`. -/
def lpDenominator (x : ℝ) : ℝ := 1 + x + lpThird x - x * lpThird x - x ^ 3 * (1 + x) ^ 2

/-- The weight `μ₁ x + 2 μ₂ y` of the corrections `k - 1` and `k - 2` of the
optimum and of the recourse terms. -/
def lpError (x : ℝ) : ℝ := lpMuOne x * x + 2 * lpMuTwo x * lpThird x

/-- The convex combination of the three benchmarks. -/
theorem lpDenominator_eq (x : ℝ) :
    lpDenominator x = lpThird x + lpMuOne x * (1 + x) + lpMuTwo x * (1 + x + lpThird x) := by
  unfold lpDenominator lpThird lpMuOne lpMuTwo
  ring

/-- The identity of Appendix A.2: `1 + x + y - x y - y²/x - (1 + x - y)(1 + x y) = y Φ(x)`. -/
theorem lpDenominator_sub (x : ℝ) :
    lpDenominator x - lpNumerator x * (1 + x ^ 3 * (1 + x)) = lpThird x * phi x := by
  unfold lpDenominator lpNumerator lpThird phi
  ring

/-- `u₁ (1 + u₁) < 1` for the root `u₁` of `Φ` in `(0, 1)`: by
`Φ(x) = (x² + x - 1)(x² - 1) + 1 - 2x`. -/
theorem root_sum_lt_one {u₁ : ℝ} (h0 : 0 < u₁) (h1 : u₁ < 1) (hphi : phi u₁ = 0) :
    u₁ * (1 + u₁) < 1 := by
  unfold phi at hphi
  by_contra h
  have hs : 1 ≤ u₁ * (1 + u₁) := le_of_not_gt h
  have hkey : (u₁ * (1 + u₁) - 1) * (u₁ ^ 2 - 1) = 2 * u₁ - 1 := by linear_combination hphi
  have hneg : (u₁ * (1 + u₁) - 1) * (u₁ ^ 2 - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  have hhalf : u₁ ≤ 1 / 2 := by linarith
  nlinarith

/-- The bound of the linear program with the error terms. At the root `x` of
`Φ`, with recourse `C ≤ ε k` and `1 ≤ ε k`, the ratio
`ρ = 1/(1 + x³ (1 + x)) + 12 ε` satisfies `k N + (μ₁ x + 2 μ₂ y) C ≤
ρ (k (1 + x + y - x y - y²/x) - (μ₁ x + 2 μ₂ y))`. On the left are the recourse
terms of the time bounds; on the right, the corrections `k - 1` and `k - 2` of
the optima enter the denominator with a minus sign, as in Appendix A.2. -/
theorem lp_bound {x ε k C : ℝ} (hx0 : 0 < x) (hs : x * (1 + x) ≤ 1) (hphi : phi x = 0)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 6) (hk : 0 < k) (hεk : 1 ≤ ε * k) (hC0 : 0 ≤ C)
    (hC : C ≤ ε * k) :
    k * lpNumerator x + lpError x * C ≤
      (1 / (1 + x ^ 3 * (1 + x)) + 12 * ε) * (k * lpDenominator x - lpError x) := by
  set q := x ^ 3 * (1 + x) with hq
  set r := 1 / (1 + q) with hr
  have hq0 : 0 ≤ q := by positivity
  have hrq : r * (1 + q) = 1 := by rw [hr]; field_simp
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one (by positivity)]; linarith
  have hx1 : x ≤ 1 := by nlinarith
  have hy0 : 0 ≤ lpThird x := by unfold lpThird; positivity
  have hyx : lpThird x ≤ x := by unfold lpThird; nlinarith
  have hy1 : lpThird x ≤ 1 := by linarith
  have hμ₁0 : 0 ≤ lpMuOne x := by
    unfold lpMuOne
    have : 0 ≤ 1 - x := by linarith
    positivity
  have hμ₁1 : lpMuOne x * x ≤ 1 := by
    unfold lpMuOne
    have h1 : x * (1 + x) * (1 - x) ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h1 hx1 hx0.le zero_le_one]
  have hμ₂0 : 0 ≤ lpMuTwo x := by unfold lpMuTwo; linarith
  have hμ₂1 : lpMuTwo x ≤ 1 := by unfold lpMuTwo; nlinarith
  have hη0 : 0 ≤ lpError x := by unfold lpError; positivity
  have hη3 : lpError x ≤ 3 := by
    unfold lpError
    nlinarith [mul_le_mul hμ₂1 hy1 hy0 zero_le_one]
  have hN1 : 1 ≤ lpNumerator x := by unfold lpNumerator; linarith
  -- `Den = N (1 + x y)`, since `Φ(x) = 0`.
  have hden : lpNumerator x * (1 + q) = lpDenominator x := by
    have := lpDenominator_sub x
    rw [hphi, mul_zero] at this
    linarith
  set P := lpNumerator x * (1 + q) with hP
  have hP1 : 1 ≤ P := by nlinarith
  have hrP : r * P = lpNumerator x := by rw [hP]; linear_combination lpNumerator x * hrq
  -- `k Den - η ≥ k (P - 3 ε) ≥ 0`.
  have hbase : k * (P - 3 * ε) ≤ k * lpDenominator x - lpError x := by
    have h2 : 3 ≤ 3 * (ε * k) := by linarith
    have h3 : k * (P - 3 * ε) = k * P - 3 * (ε * k) := by ring
    rw [h3, ← hden]
    linarith
  have hbase0 : 0 ≤ k * (P - 3 * ε) := mul_nonneg hk.le (by linarith)
  have hstep : (r + 12 * ε) * (k * (P - 3 * ε)) ≤
      (r + 12 * ε) * (k * lpDenominator x - lpError x) :=
    mul_le_mul_of_nonneg_left hbase (by linarith)
  have hexpand : (r + 12 * ε) * (k * (P - 3 * ε)) =
      k * (lpNumerator x - 3 * ε * r + 12 * ε * P - 36 * ε ^ 2) := by
    linear_combination k * hrP
  have hgain : k * (lpNumerator x + 3 * ε) ≤ (r + 12 * ε) * (k * (P - 3 * ε)) := by
    rw [hexpand]
    apply mul_le_mul_of_nonneg_left _ hk.le
    nlinarith
  have hlhs : k * lpNumerator x + lpError x * C ≤ k * (lpNumerator x + 3 * ε) := by
    have h1 : lpError x * C ≤ 3 * (ε * k) := mul_le_mul hη3 hC hC0 (by norm_num)
    have h2 : k * (lpNumerator x + 3 * ε) = k * lpNumerator x + 3 * (ε * k) := by ring
    rw [h2]
    linarith
  linarith

end ConsistentSubmodular.HardInstance
