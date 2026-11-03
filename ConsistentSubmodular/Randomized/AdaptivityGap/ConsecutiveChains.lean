module

public import ConsistentSubmodular.Randomized.Constants

@[expose] public section

/-!
# Chains in the proof of Lemma 4

The numerical core of Lemma 4 (Appendix A.6): for every chain
`d_0 ≥ d_1 ≥ ... ≥ d_N = 1`, the edge values `φ(x, y) = 1 - y/x - q (x - 1)` satisfy
`Σ_j φ(d_j, d_{j+1}) ≤ q`, which is inequality (14).

* `twoEdge_le` is inequality (15), proved as in the paper: the ratio
  `R(x, y) = (2 - y/x - 1/y) / (x + y - 1)` attains its maximum at an interior
  point, whose first-order conditions give a root of `Φ` and hence `Q(q₀) = 0`.
* `collapse_le` is inequality (16).
* `chainValue_le` controls chains of arbitrary length: nonpositive edges are
  deleted, the tail after `d_2` collapses to one edge, and three-edge chains
  are bounded by (16) and (15) or by the arithmetic–geometric mean inequality.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- The edge value `φ(x, y) = 1 - y/x - q (x - 1)`. -/
def edgeValue (x y : ℝ) : ℝ := 1 - y / x - qStar * (x - 1)

/-- The ratio `R(x, y) = (2 - y/x - 1/y) / (x + y - 1)`. -/
def twoEdgeRatio (x y : ℝ) : ℝ := (2 - y / x - 1 / y) / (x + y - 1)

/-! ### Inequality (15): the two-edge chain -/

/-- The compact region `{1 ≤ y ≤ x ≤ 8}`, which contains the maximum of `R`. -/
def ratioRegion : Set (ℝ × ℝ) := {p | 1 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 8}

theorem isCompact_ratioRegion : IsCompact ratioRegion := by
  have hclosed : IsClosed ratioRegion := by
    have h1 : IsClosed {p : ℝ × ℝ | 1 ≤ p.2} := isClosed_le continuous_const continuous_snd
    have h2 : IsClosed {p : ℝ × ℝ | p.2 ≤ p.1} := isClosed_le continuous_snd continuous_fst
    have h3 : IsClosed {p : ℝ × ℝ | p.1 ≤ 8} := isClosed_le continuous_fst continuous_const
    exact h1.inter (h2.inter h3)
  refine (isCompact_Icc (a := ((1 : ℝ), (1 : ℝ))) (b := ((8 : ℝ), (8 : ℝ)))).of_isClosed_subset
    hclosed ?_
  rintro ⟨x, y⟩ ⟨hy, hyx, hx⟩
  exact ⟨⟨by simp only; linarith, by simpa using hy⟩, ⟨by simpa using hx, by simp only; linarith⟩⟩

theorem continuousOn_twoEdgeRatio :
    ContinuousOn (fun p : ℝ × ℝ => twoEdgeRatio p.1 p.2) ratioRegion := by
  intro p hp
  obtain ⟨hy, hyx, -⟩ := hp
  have hx0 : p.1 ≠ 0 := by linarith
  have hy0 : p.2 ≠ 0 := by linarith
  have hd0 : p.1 + p.2 - 1 ≠ 0 := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold twoEdgeRatio
  fun_prop (disch := assumption)

/-- `R(x, y) ≤ 2/x`. -/
theorem twoEdgeRatio_le_two_div {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    twoEdgeRatio x y ≤ 2 / x := by
  have hx : 0 < x := by linarith
  unfold twoEdgeRatio
  rw [div_le_div_iff₀ (by linarith) hx]
  have h1 : 0 < y / x := div_pos (by linarith) hx
  have h2 : 0 < 1 / y := one_div_pos.mpr (by linarith)
  nlinarith

/-- On the boundary `y = 1`, `R(x, 1) = (x - 1)/x² ≤ 1/4`. -/
theorem twoEdgeRatio_one_le {x : ℝ} (hx : 1 ≤ x) : twoEdgeRatio x 1 ≤ 1 / 4 := by
  unfold twoEdgeRatio
  rw [div_le_iff₀ (by linarith)]
  have hx0 : 0 < x := by linarith
  have h : 1 / x ≥ 1 - x / 4 := by
    rw [ge_iff_le, le_div_iff₀ hx0]
    nlinarith [sq_nonneg (x - 2)]
  nlinarith

/-- On the boundary `y = x`, `R(x, x) = (1 - 1/x)/(2x - 1) ≤ 1/4`. -/
theorem twoEdgeRatio_diag_le {x : ℝ} (hx : 1 ≤ x) : twoEdgeRatio x x ≤ 1 / 4 := by
  have hx0 : 0 < x := by linarith
  unfold twoEdgeRatio
  rw [div_self hx0.ne', div_le_iff₀ (by linarith)]
  have h : 1 / x ≥ 1 - (2 * x - 1) / 4 := by
    rw [ge_iff_le, le_div_iff₀ hx0]
    nlinarith [sq_nonneg (x - 5 / 4)]
  linarith

/-- The derivative of `t ↦ R(t, y)`. -/
theorem hasDerivAt_twoEdgeRatio_fst {x y : ℝ} (hx : 0 < x) (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun t => twoEdgeRatio t y)
      ((y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) x := by
  have hN : HasDerivAt (fun t => 2 - y / t - 1 / y) (y / x ^ 2) x := by
    have h := ((hasDerivAt_const x (2 : ℝ)).sub
      ((hasDerivAt_const x y).div (hasDerivAt_id x) hx.ne')).sub_const (1 / y)
    convert h using 1
    simp only [id]
    field_simp
    ring
  have hDer : HasDerivAt (fun t => t + y - 1) 1 x := ((hasDerivAt_id x).add_const y).sub_const 1
  have h := hN.div hDer hD
  convert h using 1
  ring

/-- The derivative of `s ↦ R(x, s)`. -/
theorem hasDerivAt_twoEdgeRatio_snd {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hD : x + y - 1 ≠ 0) :
    HasDerivAt (fun s => twoEdgeRatio x s)
      (((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2) y := by
  have hN : HasDerivAt (fun s => 2 - s / x - 1 / s) (1 / y ^ 2 - 1 / x) y := by
    have h := ((hasDerivAt_const y (2 : ℝ)).sub ((hasDerivAt_id y).div_const x)).sub
      ((hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy.ne')
    convert h using 1
    simp only [id]
    field_simp
    ring
  have hDer : HasDerivAt (fun s => x + s - 1) 1 y := ((hasDerivAt_id y).const_add x).sub_const 1
  have h := hN.div hDer hD
  convert h using 1
  ring

/-- The first-order conditions at an interior maximum `(x, y)` of `R`. With
`u = y/x` and `v = 1/x` they give `v = u² (1 + u)` and `Φ(u) = 0`, so that
`R(x, y) = y/x² = u v = u³ (1 + u)`. -/
theorem twoEdgeRatio_critical {x y : ℝ} (hy : 1 < y) (hyx : y < x)
    (hfx : (y / x ^ 2 * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0)
    (hfy : ((1 / y ^ 2 - 1 / x) * (x + y - 1) - (2 - y / x - 1 / y)) / (x + y - 1) ^ 2 = 0) :
    phi (y / x) = 0 ∧ twoEdgeRatio x y = y / x ^ 2 ∧
      twoEdgeRatio x y = (y / x) ^ 3 * (1 + y / x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hD : 0 < x + y - 1 := by linarith
  have hD2 : (x + y - 1) ^ 2 ≠ 0 := by positivity
  have hNx : 2 - y / x - 1 / y = y / x ^ 2 * (x + y - 1) := by
    have := (div_eq_zero_iff.mp hfx).resolve_right hD2
    linarith
  have hNy : 2 - y / x - 1 / y = (1 / y ^ 2 - 1 / x) * (x + y - 1) := by
    have := (div_eq_zero_iff.mp hfy).resolve_right hD2
    linarith
  -- Equating the two expressions for `R` gives `E₁ = 0`; `R = y/x²` gives `E₂ = 0`.
  have hE₁ : x ^ 2 - x * y ^ 2 - y ^ 3 = 0 := by
    have h' : y / x ^ 2 = 1 / y ^ 2 - 1 / x := mul_right_cancel₀ hD.ne' (hNx.symm.trans hNy)
    have hid : y / x ^ 2 - (1 / y ^ 2 - 1 / x) = -(x ^ 2 - x * y ^ 2 - y ^ 3) / (x ^ 2 * y ^ 2) := by
      field_simp
      ring
    have h0 : -(x ^ 2 - x * y ^ 2 - y ^ 3) / (x ^ 2 * y ^ 2) = 0 := by
      rw [← hid, h', sub_self]
    have := (div_eq_zero_iff.mp h0).resolve_right (by positivity)
    linarith
  have hE₂ : 2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2 = 0 := by
    have hid : 2 - y / x - 1 / y - y / x ^ 2 * (x + y - 1) =
        (2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2) / (x ^ 2 * y) := by
      field_simp
      ring
    have h0 : (2 * x ^ 2 * y - 2 * x * y ^ 2 - x ^ 2 - y ^ 3 + y ^ 2) / (x ^ 2 * y) = 0 := by
      rw [← hid, hNx, sub_self]
    exact (div_eq_zero_iff.mp h0).resolve_right (by positivity)
  have hG : y * (y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4) = 0 := by
    linear_combination (x ^ 2 - y ^ 2) * hE₁ + x ^ 2 * hE₂
  have hG' : y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4 = 0 :=
    (mul_eq_zero.mp hG).resolve_left hy0.ne'
  have hR : twoEdgeRatio x y = y / x ^ 2 := by
    unfold twoEdgeRatio
    rw [hNx, mul_div_assoc, div_self hD.ne', mul_one]
  refine ⟨?_, hR, ?_⟩
  · have hid : phi (y / x) =
        (y ^ 4 + x * y ^ 3 - 2 * x ^ 2 * y ^ 2 - 3 * x ^ 3 * y + 2 * x ^ 4) / x ^ 4 := by
      unfold phi
      field_simp
    rw [hid, hG', zero_div]
  · have hid : y / x ^ 2 - (y / x) ^ 3 * (1 + y / x) = y * (x ^ 2 - x * y ^ 2 - y ^ 3) / x ^ 4 := by
      field_simp
      ring
    rw [hR, ← sub_eq_zero, hid, hE₁, mul_zero, zero_div]

/-- **Inequality (15)**, as `R(x, y) ≤ q` for `1 ≤ y ≤ x`: the maximum of `R` is
attained at an interior point of `{1 ≤ y ≤ x ≤ 8}`, and there it is a root of
`Q` in `[0, 1]`, hence equal to `q`. -/
theorem twoEdgeRatio_le {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) : twoEdgeRatio x y ≤ qStar := by
  obtain ⟨p, hpK, hmax⟩ := isCompact_ratioRegion.exists_isMaxOn
    ⟨((2 : ℝ), (6 / 5 : ℝ)), by norm_num [ratioRegion]⟩ continuousOn_twoEdgeRatio
  have hmax' : ∀ a b : ℝ, (a, b) ∈ ratioRegion → twoEdgeRatio a b ≤ twoEdgeRatio p.1 p.2 :=
    fun a b hab => isMaxOn_iff.mp hmax (a, b) hab
  obtain ⟨hy1, hyx', hx8⟩ := hpK
  -- `R(2, 6/5) = 17/66 > 1/4`, so the maximum is not on the boundary.
  have hR0 : (17 : ℝ) / 66 ≤ twoEdgeRatio p.1 p.2 := by
    have h := hmax' 2 (6 / 5) (by norm_num [ratioRegion])
    have h2 : twoEdgeRatio 2 (6 / 5) = 17 / 66 := by norm_num [twoEdgeRatio]
    linarith
  have hy1' : 1 < p.2 := by
    rcases eq_or_lt_of_le hy1 with h | h
    · rw [← h] at hR0
      have := twoEdgeRatio_one_le (show 1 ≤ p.1 by linarith)
      linarith
    · exact h
  have hyx'' : p.2 < p.1 := by
    rcases eq_or_lt_of_le hyx' with h | h
    · rw [h] at hR0
      have := twoEdgeRatio_diag_le (show 1 ≤ p.1 by linarith)
      linarith
    · exact h
  have hx8' : p.1 < 8 := by
    rcases eq_or_lt_of_le hx8 with h | h
    · have := twoEdgeRatio_le_two_div hy1 hyx'
      rw [h] at this hR0
      linarith
    · exact h
  have hx0 : 0 < p.1 := by linarith
  have hy0 : 0 < p.2 := by linarith
  have hD : p.1 + p.2 - 1 ≠ 0 := by linarith
  -- The first-order conditions at the interior maximum.
  have hlocx : IsLocalMax (fun t => twoEdgeRatio t p.2) p.1 := by
    filter_upwards [Ioo_mem_nhds hyx'' hx8'] with t ht
    exact hmax' t p.2 ⟨hy1, ht.1.le, ht.2.le⟩
  have hlocy : IsLocalMax (fun s => twoEdgeRatio p.1 s) p.2 := by
    filter_upwards [Ioo_mem_nhds hy1' hyx''] with s hs
    exact hmax' p.1 s ⟨hs.1.le, hs.2.le, hx8⟩
  obtain ⟨hphi, hR, hRu⟩ := twoEdgeRatio_critical hy1' hyx''
    (hlocx.hasDerivAt_eq_zero (hasDerivAt_twoEdgeRatio_fst hx0 hD))
    (hlocy.hasDerivAt_eq_zero (hasDerivAt_twoEdgeRatio_snd hx0 hy0 hD))
  -- With `u = y/x`: `R = u³ (1 + u) = 2u² + 3u - 2`, a root of `Q` in `[0, 1]`.
  have hRu' : twoEdgeRatio p.1 p.2 = 2 * (p.2 / p.1) ^ 2 + 3 * (p.2 / p.1) - 2 := by
    rw [hRu]
    unfold phi at hphi
    linear_combination hphi
  have hQ : quartic (twoEdgeRatio p.1 p.2) = 0 := by
    rw [hRu', quartic_comp, hphi, zero_mul]
  have hR1 : twoEdgeRatio p.1 p.2 ≤ 1 := by
    rw [hR, div_le_one (by positivity)]
    nlinarith
  have hRq : twoEdgeRatio p.1 p.2 = qStar :=
    eq_qStar (by rw [hR]; positivity) hR1 hQ
  by_cases hx : x ≤ 8
  · exact hRq ▸ hmax' x y ⟨hy, hyx, hx⟩
  · have h := twoEdgeRatio_le_two_div hy hyx
    have h' : 2 / x ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith [qStar_bounds.1]

/-- **Inequality (15)**: `φ(x, y) + φ(y, 1) ≤ q` for `x ≥ y ≥ 1`. -/
theorem twoEdge_le {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y 1 ≤ qStar := by
  have h := twoEdgeRatio_le hy hyx
  have hD : 0 < x + y - 1 := by linarith
  unfold twoEdgeRatio at h
  rw [div_le_iff₀ hD] at h
  unfold edgeValue
  linarith

/-! ### Inequality (16) and the bounds for positive edges -/

/-- The collapse threshold `L = 1/(1 - q)`. -/
def collapseBound : ℝ := 1 / (1 - qStar)

theorem one_sub_qStar_pos : 0 < 1 - qStar := by linarith [qStar_bounds.2]

theorem four_thirds_lt_collapseBound : (4 : ℝ) / 3 < collapseBound := by
  rw [collapseBound, lt_div_iff₀ one_sub_qStar_pos]
  linarith [qStar_bounds.1]

/-- **Inequality (16)**: if `1 ≤ z ≤ y ≤ x ≤ L`, then `φ(x, y) + φ(y, z) ≤ φ(x, z)`. -/
theorem collapse_le {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x)
    (hxL : x ≤ collapseBound) : edgeValue x y + edgeValue y z ≤ edgeValue x z := by
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 - qStar ≤ 1 / x := by
    rw [collapseBound, le_div_iff₀ one_sub_qStar_pos] at hxL
    rw [le_div_iff₀ hx0]
    linarith
  have hid : edgeValue x y + edgeValue y z - edgeValue x z =
      (y - z) * (1 / y - 1 / x) - qStar * (y - 1) := by
    unfold edgeValue
    field_simp
    ring
  have ha : 0 ≤ 1 / y - 1 / x := by
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hy0 hyx
  have hb : 1 / y ≤ 1 := by
    rw [div_le_one hy0]
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hz) ha, mul_nonneg (show 0 ≤ y - 1 by linarith)
    (sub_nonneg.mpr hb), mul_nonneg (show 0 ≤ y - 1 by linarith) (sub_nonneg.mpr hx1)]

/-- A positive edge `x → y` has `y < h(x) = (1 + q) x - q x²`. -/
theorem lt_of_edgeValue_pos {x y : ℝ} (hx : 0 < x) (h : 0 < edgeValue x y) :
    y < (1 + qStar) * x - qStar * x ^ 2 := by
  unfold edgeValue at h
  have h' : y / x < 1 - qStar * (x - 1) := by linarith
  rw [div_lt_iff₀ hx] at h'
  nlinarith

/-- The second vertex of a positive edge satisfies `d_1 < T < 31/20`, where
`T = (1 + q)²/(4q)` is the maximum of `h`; the bound on `T` uses (13). -/
theorem second_lt {x y : ℝ} (hx : 1 ≤ x) (h : 0 < edgeValue x y) : y < 31 / 20 := by
  have hq := qStar_bounds
  have hy := lt_of_edgeValue_pos (by linarith) h
  nlinarith [sq_nonneg (2 * qStar * x - (1 + qStar)),
    mul_pos (sub_pos.mpr hq.1) (sub_pos.mpr hq.2)]

/-- The third vertex of a chain with two positive edges satisfies
`d_2 < h(31/20) = 31/20 - 341 q/400 < 4/3`, because `h` increases on `[1, 31/20]`
by (13). -/
theorem third_lt {y z : ℝ} (hy : 1 ≤ y) (hy' : y < 31 / 20) (h : 0 < edgeValue y z) :
    z < 4 / 3 := by
  have hq := qStar_bounds
  have hz := lt_of_edgeValue_pos (by linarith) h
  have hinc : 0 ≤ 1 + qStar - qStar * (31 / 20 + y) := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 31 / 20 - y by linarith) hinc]

/-! ### Three-edge chains -/

/-- The arithmetic–geometric mean inequality `a x + b/x ≥ 2 √(a b)`. -/
theorem two_sqrt_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 < x) :
    2 * Real.sqrt (a * b) ≤ a * x + b / x := by
  have h1 : Real.sqrt (a * x) ^ 2 = a * x := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt (b / x) ^ 2 = b / x := Real.sq_sqrt (by positivity)
  have h3 : Real.sqrt (a * x) * Real.sqrt (b / x) = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  nlinarith [sq_nonneg (Real.sqrt (a * x) - Real.sqrt (b / x))]

/-- The bound `F(y) = 3 + 3q - q y - 2 √(q y) - 2 √(q + 1/y)` on three-edge chains
through `y`. -/
def threeEdgeBound (y : ℝ) : ℝ :=
  3 + 3 * qStar - qStar * y - 2 * Real.sqrt (qStar * y) - 2 * Real.sqrt (qStar + 1 / y)

/-- The arithmetic–geometric mean inequality in `x` and in `z` bounds a three-edge
chain `x → y → z → 1` by `F(y)`. -/
theorem threeEdge_le_bound {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y z + edgeValue z 1 ≤ threeEdgeBound y := by
  have hq := qStar_pos
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < z := by linarith
  have hid : edgeValue x y + edgeValue y z + edgeValue z 1 =
      3 + 3 * qStar - qStar * y - (qStar * x + y / x) - ((qStar + 1 / y) * z + 1 / z) := by
    unfold edgeValue
    field_simp
    ring
  have h1 := two_sqrt_le hq.le hy0.le hx0
  have h2 := two_sqrt_le (a := qStar + 1 / y) (b := 1) (by positivity) zero_le_one hz0
  rw [mul_one] at h2
  rw [hid, threeEdgeBound]
  linarith

theorem hasDerivAt_threeEdgeBound {y : ℝ} (hy : 0 < y) :
    HasDerivAt threeEdgeBound
      (-qStar - qStar / Real.sqrt (qStar * y) + 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y))) y := by
  have hq := qStar_pos
  have hqy : qStar * y ≠ 0 := (mul_pos hq hy).ne'
  have hqy' : qStar + 1 / y ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t => Real.sqrt (qStar * t)) (qStar / (2 * Real.sqrt (qStar * y))) y := by
    have := ((hasDerivAt_id y).const_mul qStar).sqrt (by simpa using hqy)
    simpa using this
  have h2 : HasDerivAt (fun t => Real.sqrt (qStar + 1 / t))
      (-(1 / y ^ 2) / (2 * Real.sqrt (qStar + 1 / y))) y := by
    have hinv : HasDerivAt (fun t => qStar + 1 / t) (-(1 / y ^ 2)) y := by
      have := (hasDerivAt_inv hy.ne').const_add qStar
      simpa [one_div] using this
    exact hinv.sqrt hqy'
  have h := ((((hasDerivAt_const y (3 + 3 * qStar)).sub ((hasDerivAt_id y).const_mul qStar)).sub
    (h1.const_mul 2)).sub (h2.const_mul 2))
  convert h using 1
  have hs1 : 0 < Real.sqrt (qStar * y) := Real.sqrt_pos.mpr (mul_pos hq hy)
  have hs2 : 0 < Real.sqrt (qStar + 1 / y) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

/-- `F` decreases on `[L, ∞)`: there `F'(y) ≤ -q - √(q/y) + y^{-3/2} < 0`, because
`q y^{3/2} + √q y > 1` for `q > 1/4` and `y > 4/3`. -/
theorem threeEdgeBound_antitoneOn : AntitoneOn threeEdgeBound (Set.Ici collapseBound) := by
  have hq := qStar_bounds
  have hL := four_thirds_lt_collapseBound
  have hderiv : ∀ y ∈ Set.Ici collapseBound, HasDerivAt threeEdgeBound
      (-qStar - qStar / Real.sqrt (qStar * y) + 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y))) y :=
    fun y hy => hasDerivAt_threeEdgeBound (by linarith [Set.mem_Ici.mp hy])
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    exact fun y hy => (hderiv y (Set.mem_Ici.mpr (Set.mem_Ioi.mp hy).le)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy
    have hyL : collapseBound < y := hy
    have hy0 : 0 < y := by linarith
    rw [(hderiv y (Set.mem_Ici.mpr hyL.le)).deriv]
    set w := Real.sqrt y with hw
    have hw0 : 0 < w := Real.sqrt_pos.mpr hy0
    have hw2 : w ^ 2 = y := Real.sq_sqrt hy0.le
    have hsq : Real.sqrt (qStar * y) = Real.sqrt qStar * w := Real.sqrt_mul qStar_pos.le y
    have hsq0 : 1 / 2 < Real.sqrt qStar := by
      rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hs : 1 / w ≤ Real.sqrt (qStar + 1 / y) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, one_pow, hw2]
      linarith [qStar_pos]
    have hs0 : 0 < Real.sqrt (qStar + 1 / y) := lt_of_lt_of_le (by positivity) hs
    -- `1 / (y² s) ≤ 1 / w³`
    have hterm : 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y)) ≤ 1 / w ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      have : w ^ 3 = y ^ 2 * (1 / w) := by
        rw [← hw2]
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hw43 : 4 / 3 < w ^ 2 := by linarith
    have hw1 : 23 / 20 < w := by nlinarith
    have hw3 : 23 / 15 < w ^ 3 := by
      have : w ^ 3 = w * w ^ 2 := by ring
      rw [this]
      nlinarith
    have hqw3 : 259 / 1000 * (23 / 15) < qStar * w ^ 3 :=
      mul_lt_mul'' hq.1 hw3 (by norm_num) (by norm_num)
    have hsqw2 : 1 / 2 * (4 / 3) < Real.sqrt qStar * w ^ 2 :=
      mul_lt_mul'' hsq0 hw43 (by norm_num) (by norm_num)
    have hkey : 1 ≤ qStar * w ^ 3 + Real.sqrt qStar * w ^ 2 := by linarith
    have hfrac : 1 / w ^ 3 ≤ qStar + qStar / (Real.sqrt qStar * w) := by
      have hsqpos : 0 < Real.sqrt qStar := Real.sqrt_pos.mpr qStar_pos
      rw [div_le_iff₀ (by positivity)]
      have hsimp : (qStar + qStar / (Real.sqrt qStar * w)) * w ^ 3 =
          qStar * w ^ 3 + qStar / Real.sqrt qStar * w ^ 2 := by
        field_simp
      rw [hsimp, Real.div_sqrt]
      exact hkey
    rw [hsq]
    linarith

/-- `F(L) = φ(x⋆, L) + φ(L, 1) ≤ q` with `x⋆ = √(L/q) ≥ L`: equality holds in both
arithmetic–geometric mean inequalities at `(x⋆, L, 1)`, and (15) applies. -/
theorem threeEdgeBound_collapseBound_le : threeEdgeBound collapseBound ≤ qStar := by
  have hq := qStar_bounds
  have hq0 := qStar_pos
  have hL := four_thirds_lt_collapseBound
  have hL0 : 0 < collapseBound := by linarith
  have hqL : qStar + 1 / collapseBound = 1 := by
    rw [collapseBound, one_div_one_div]
    ring
  set r := Real.sqrt (qStar * collapseBound) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (mul_pos hq0 hL0)
  have hr2 : r ^ 2 = qStar * collapseBound := Real.sq_sqrt (mul_pos hq0 hL0).le
  -- `x⋆ = r/q = √(L/q)`, and `x⋆ ≥ L` because `q L < 1`.
  have hqL1 : qStar * collapseBound < 1 := by
    rw [collapseBound, mul_one_div, div_lt_one one_sub_qStar_pos]
    linarith
  have hxL : collapseBound ≤ r / qStar := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have h17 := twoEdge_le (x := r / qStar) (y := collapseBound) (by linarith) hxL
  have hval : threeEdgeBound collapseBound = edgeValue (r / qStar) collapseBound +
      edgeValue collapseBound 1 := by
    have hL1 : 1 / collapseBound = 1 - qStar := by
      rw [collapseBound, one_div_one_div]
    have hdiv : collapseBound / (r / qStar) = r := by
      rw [div_div_eq_mul_div, div_eq_iff hr0.ne']
      linear_combination (-1 : ℝ) * hr2
    have hmul : qStar * (r / qStar) = r := by
      field_simp
    rw [threeEdgeBound, hqL, Real.sqrt_one, ← hr]
    unfold edgeValue
    rw [hdiv, hL1, mul_sub, hmul]
    ring
  linarith

/-- Three-edge chains `x → y → z → 1` have value at most `q`: by (16) and (15) if
`y ≤ L`, and by `F(y) ≤ F(L) ≤ q` if `y ≥ L`. -/
theorem threeEdge_le {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y z + edgeValue z 1 ≤ qStar := by
  rcases le_total y collapseBound with hyL | hyL
  · have h18 := collapse_le (le_refl 1) hz hzy hyL
    have h17 := twoEdge_le (le_trans hz hzy) hyx
    linarith
  · have hF := threeEdge_le_bound hz hzy hyx
    have hmono := threeEdgeBound_antitoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hyL) hyL
    linarith [threeEdgeBound_collapseBound_le]

/-! ### Chains of arbitrary length -/

/-- The value `Σ_j φ(d_j, d_{j+1})` of the chain `d_0, ..., d_N`. -/
def chainValue : List ℝ → ℝ
  | x :: y :: rest => edgeValue x y + chainValue (y :: rest)
  | _ => 0

theorem chainValue_cons_cons (x y : ℝ) (rest : List ℝ) :
    chainValue (x :: y :: rest) = edgeValue x y + chainValue (y :: rest) := rfl

/-- A chain `d_0 ≥ d_1 ≥ ... ≥ d_N = 1`. -/
def IsDescendingChain (L : List ℝ) : Prop :=
  L.IsChain (fun a b => b ≤ a) ∧ (∀ w ∈ L, 1 ≤ w) ∧ L.getLast? = some 1

namespace IsDescendingChain

variable {x y z : ℝ} {rest : List ℝ}

theorem le_head (h : IsDescendingChain (x :: y :: rest)) : y ≤ x :=
  (List.isChain_cons_cons.mp h.1).1

theorem one_le {L : List ℝ} (h : IsDescendingChain L) {w : ℝ} (hw : w ∈ L) : 1 ≤ w :=
  h.2.1 w hw

theorem tail (h : IsDescendingChain (x :: y :: rest)) : IsDescendingChain (y :: rest) :=
  ⟨(List.isChain_cons_cons.mp h.1).2, fun w hw => h.2.1 w (List.mem_cons_of_mem x hw),
    by rw [← List.getLast?_cons_cons (a := x)]; exact h.2.2⟩

/-- Deleting the vertex `y` of `x → y → z` keeps a chain. -/
theorem skip (h : IsDescendingChain (x :: y :: z :: rest)) : IsDescendingChain (x :: z :: rest) := by
  have hyx := h.le_head
  have hzy := h.tail.le_head
  refine ⟨List.isChain_cons_cons.mpr ⟨hzy.trans hyx, (List.isChain_cons_cons.mp h.1).2.tail⟩, ?_, ?_⟩
  · intro w hw
    apply h.2.1
    simp only [List.mem_cons] at hw ⊢
    tauto
  · rw [List.getLast?_cons_cons]
    have h2 := h.2.2
    rw [List.getLast?_cons_cons, List.getLast?_cons_cons] at h2
    exact h2

theorem eq_one_of_singleton (h : IsDescendingChain [x]) : x = 1 := by
  have h2 := h.2.2
  rw [List.getLast?_singleton] at h2
  exact Option.some.inj h2

end IsDescendingChain

/-- The tail after a vertex `z ≤ L` collapses to the single edge `z → 1` by (16). -/
theorem tail_le (z : ℝ) (rest : List ℝ) (h : IsDescendingChain (z :: rest))
    (hzL : z ≤ collapseBound) : chainValue (z :: rest) ≤ edgeValue z 1 := by
  induction rest generalizing z with
  | nil =>
    rw [h.eq_one_of_singleton]
    simp [chainValue, edgeValue]
  | cons y rest ih =>
    have hyz := h.le_head
    have hy1 : 1 ≤ y := h.one_le (by simp)
    rw [chainValue_cons_cons]
    have hih := ih y h.tail (hyz.trans hzL)
    have h18 := collapse_le (le_refl 1) hy1 hyz hzL
    linarith

/-- Chains of arbitrary length: `Σ_j φ(d_j, d_{j+1}) ≤ q` for every chain
`d_0 ≥ ... ≥ d_N = 1`. Deleting the starting vertex of a nonpositive edge does not
decrease the value; only the first two edges need to be positive, which gives
`d_2 < 4/3 < L`, so the tail after `d_2` collapses by (16) and the three-edge bound
applies. -/
theorem chainValue_le (L : List ℝ) (hL : IsDescendingChain L) : chainValue L ≤ qStar := by
  induction h : L.length using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    match L, hL with
    | [], _ => exact qStar_pos.le
    | [_], _ => exact qStar_pos.le
    | x :: y :: rest, hL =>
      have hyx := hL.le_head
      have hx1 : 1 ≤ x := hL.one_le (by simp)
      have hy1 : 1 ≤ y := hL.one_le (by simp)
      rw [chainValue_cons_cons]
      by_cases h1 : edgeValue x y ≤ 0
      · -- Delete the first vertex.
        have := ih (y :: rest).length (by simp [← h]) (y :: rest) hL.tail rfl
        linarith
      · rw [not_le] at h1
        cases rest with
        | nil =>
          have hy : y = 1 := hL.tail.eq_one_of_singleton
          subst hy
          have h17 := twoEdge_le (le_refl 1) hx1
          simp only [chainValue, edgeValue] at h17 ⊢
          norm_num at h17 ⊢
          linarith
        | cons z rest' =>
          have hzy := hL.tail.le_head
          have hz1 : 1 ≤ z := hL.one_le (by simp)
          rw [chainValue_cons_cons]
          by_cases h2 : edgeValue y z ≤ 0
          · -- Delete the second vertex: `φ(x, y) ≤ φ(x, z)`.
            have hskip := ih (x :: z :: rest').length (by simp [← h]) (x :: z :: rest') hL.skip rfl
            rw [chainValue_cons_cons] at hskip
            have hxz : edgeValue x y ≤ edgeValue x z := by
              unfold edgeValue
              have : z / x ≤ y / x := div_le_div_of_nonneg_right hzy (by linarith)
              linarith
            linarith
          · rw [not_le] at h2
            have hz' := third_lt hy1 (second_lt hx1 h1) h2
            have htail := tail_le z rest' hL.tail.tail
              (by linarith [four_thirds_lt_collapseBound])
            have h3 := threeEdge_le hz1 hzy hyx
            linarith

theorem chainValue_ofFn {N : ℕ} (z : Fin (N + 1) → ℝ) :
    chainValue (List.ofFn z) = ∑ j : Fin N, edgeValue (z j.castSucc) (z j.succ) := by
  induction N with
  | zero => simp [chainValue]
  | succ N ih =>
    rw [List.ofFn_succ, List.ofFn_succ, chainValue_cons_cons, Fin.sum_univ_succ]
    have h := ih (fun i => z i.succ)
    rw [List.ofFn_succ] at h
    rw [h]
    rfl

/-- **Inequality (14)**: for a chain `d_0 ≥ ... ≥ d_N = 1`,
`Σ_j (1 - d_{j+1}/d_j) - q Σ_j (d_j - 1) = Σ_j φ(d_j, d_{j+1}) ≤ q`. -/
theorem sum_edgeValue_le {N : ℕ} (d : Fin (N + 1) → ℝ) (hanti : Antitone d)
    (hlast : d (Fin.last N) = 1) :
    ∑ j : Fin N, edgeValue (d j.castSucc) (d j.succ) ≤ qStar := by
  rw [← chainValue_ofFn]
  apply chainValue_le
  refine ⟨List.isChain_ofFn.mpr fun i hi => hanti (Fin.mk_le_mk.mpr (by omega)), ?_, ?_⟩
  · intro w hw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hw
    rw [← hlast]
    exact hanti (Fin.le_last i)
  · rw [List.getLast?_eq_some_getLast (by simp), List.getLast_ofFn, ← hlast]
    rfl

end ConsistentSubmodular.Chains
