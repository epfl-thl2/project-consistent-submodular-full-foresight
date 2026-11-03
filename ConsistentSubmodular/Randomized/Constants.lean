module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# The constants `ξ⋆`, `u₁`, and `q`

Proposition 1 (Appendix A.1): the polynomial `Ψ` has a unique root `ξ⋆` in
`(1/2, 1)`. Existence is the intermediate value theorem; uniqueness follows from
the strict convexity of `Ψ` on `[1/2, 1]`; and evaluating `Ψ` at two rational
points gives `0.7941970146 < ξ⋆ < 0.7941970148`.

The weight `u₁` of the hard instance (Section 2.1) is the unique root of `Φ` in
`(0, 1)`, and `ξ⋆ = 1 / (1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. The number
`q = (1 - ξ⋆) / ξ⋆ = u₁ u₂` is the unique root in `(0, 1)` of the quartic `Q` of
equation (12), and it satisfies the bounds (13).
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-! ### The polynomial `Ψ` (Proposition 1) -/

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

theorem hasDerivAt_psi (x : ℝ) :
    HasDerivAt psi (356 * x ^ 3 - 132 * x ^ 2 - 38 * x - 3) x := by
  have h := ((((hasDerivAt_pow 4 x).const_mul (89 : ℝ)).sub
    ((hasDerivAt_pow 3 x).const_mul (44 : ℝ))).sub
    ((hasDerivAt_pow 2 x).const_mul (19 : ℝ))).sub ((hasDerivAt_id x).const_mul (3 : ℝ))
  convert h.add_const (1 : ℝ) using 1
  norm_num
  ring

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- `Ψ` is strictly convex on `[1/2, 1]`: `Ψ'' > 0` there, so `Ψ'` increases. -/
theorem psi_strictConvexOn : StrictConvexOn ℝ (Set.Icc (1 / 2) 1) psi := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) continuous_psi.continuousOn
  rw [interior_Icc]
  intro a ha b hb hab
  rw [(hasDerivAt_psi a).deriv, (hasDerivAt_psi b).deriv]
  have hpos : 0 < 356 * (a ^ 2 + a * b + b ^ 2) - 132 * (a + b) - 38 := by
    nlinarith [ha.1, hb.1]
  have hkey : (356 * b ^ 3 - 132 * b ^ 2 - 38 * b - 3) - (356 * a ^ 3 - 132 * a ^ 2 - 38 * a - 3) =
      (b - a) * (356 * (a ^ 2 + a * b + b ^ 2) - 132 * (a + b) - 38) := by ring
  nlinarith [mul_pos (sub_pos.mpr hab) hpos]

/-- Uniqueness in Proposition 1: if `ξ₁ < ξ₂` were two roots in `(1/2, 1)`,
strict convexity would give `Ψ(ξ₁) < λ Ψ(1/2) + (1 - λ) Ψ(ξ₂) = λ Ψ(1/2) < 0`. -/
theorem psi_root_unique {ξ₁ ξ₂ : ℝ} (h₁ : 1 / 2 < ξ₁) (h₁' : ξ₁ < 1) (h₂ : 1 / 2 < ξ₂)
    (h₂' : ξ₂ < 1) (hψ₁ : psi ξ₁ = 0) (hψ₂ : psi ξ₂ = 0) : ξ₁ = ξ₂ := by
  have key : ∀ {a b : ℝ}, 1 / 2 < a → a < b → b < 1 → psi a = 0 → psi b = 0 → False := by
    intro a b ha hab hb hψa hψb
    set lam := (b - a) / (b - 1 / 2) with hlam
    have hden : 0 < b - 1 / 2 := by linarith
    have hlam0 : 0 < lam := div_pos (by linarith) hden
    have hlam1 : 0 < 1 - lam := by
      rw [hlam, sub_pos, div_lt_one hden]
      linarith
    have hl : lam * (b - 1 / 2) = b - a := div_mul_cancel₀ _ hden.ne'
    have hcomb : lam • (1 / 2 : ℝ) + (1 - lam) • b = a := by
      simp only [smul_eq_mul]
      linear_combination (-1 : ℝ) * hl
    have hhalf_mem : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
    have hb_mem : b ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by linarith, hb.le⟩
    have h := psi_strictConvexOn.2 hhalf_mem hb_mem (by linarith) hlam0 hlam1 (by ring)
    rw [hcomb, hψa, hψb] at h
    have hhalf : psi (1 / 2) = -83 / 16 := by norm_num [psi]
    simp only [smul_eq_mul, hhalf] at h
    nlinarith
  rcases lt_trichotomy ξ₁ ξ₂ with h | h | h
  · exact (key h₁ h h₂' hψ₁ hψ₂).elim
  · exact h
  · exact (key h₂ h h₁' hψ₂ hψ₁).elim

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

/-- The numerical value in Proposition 1: `Ψ(0.7941970146) < 0 < Ψ(0.7941970148)`,
so `Ψ` has a root between these points, and it is `ξ⋆` by uniqueness. -/
theorem xiStar_bounds : (0.7941970146 : ℝ) < xiStar ∧ xiStar < 0.7941970148 := by
  have hsub := intermediate_value_Ioo (show (0.7941970146 : ℝ) ≤ 0.7941970148 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi 0.7941970146) (psi 0.7941970148) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hψ⟩ := hsub hmem
  have h := eq_xiStar (by linarith) (by linarith) hψ
  subst h
  exact ⟨h1, h2⟩

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

/-- **Proposition 1**: `Ψ` has a unique root `ξ⋆ ∈ (1/2, 1)`, and
`0.7941970146 < ξ⋆ < 0.7941970148`. -/
theorem psiRoot : PsiRootGoal := by
  obtain ⟨h1, h2, hψ⟩ := xiStar_root
  obtain ⟨b1, b2⟩ := xiStar_bounds
  exact ⟨h1, h2, hψ, fun ξ hξ₁ hξ₂ hψξ => eq_xiStar hξ₁ hξ₂ hψξ, b1, b2⟩

/-! ### The quartic `Q` of equation (12) -/

/-- `Q(t) = t⁴ + t³ - 22 t² - 87 t + 24`, so that `Q(t) = (1 + t)⁴ Ψ(1/(1 + t))`. -/
def quartic (t : ℝ) : ℝ := t ^ 4 + t ^ 3 - 22 * t ^ 2 - 87 * t + 24

theorem quartic_eq_psi {t : ℝ} (ht : 0 < 1 + t) :
    quartic t = (1 + t) ^ 4 * psi (1 / (1 + t)) := by
  unfold quartic psi
  field_simp
  ring

theorem continuous_quartic : Continuous quartic := by
  unfold quartic
  fun_prop

theorem hasDerivAt_quartic (t : ℝ) :
    HasDerivAt quartic (4 * t ^ 3 + 3 * t ^ 2 - 44 * t - 87) t := by
  have h := ((((hasDerivAt_pow 4 t).add (hasDerivAt_pow 3 t)).sub
    ((hasDerivAt_pow 2 t).const_mul (22 : ℝ))).sub ((hasDerivAt_id t).const_mul (87 : ℝ)))
  convert h.add_const (24 : ℝ) using 1
  norm_num
  ring

/-- `Q' < 0` on `(0, 1)`, so `Q` is strictly decreasing on `[0, 1]`. -/
theorem quartic_strictAntiOn : StrictAntiOn quartic (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_quartic.continuousOn
  rw [interior_Icc]
  intro t ht
  rw [(hasDerivAt_quartic t).deriv]
  nlinarith [ht.1, ht.2, mul_pos ht.1 ht.1, mul_pos (mul_pos ht.1 ht.1) ht.1]

/-- The number `q = (1 - ξ⋆) / ξ⋆`. -/
def qStar : ℝ := (1 - xiStar) / xiStar

theorem xiStar_eq_qStar : xiStar = 1 / (1 + qStar) := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

theorem one_add_qStar : 1 + qStar = 1 / xiStar := by
  have h := xiStar_pos
  unfold qStar
  field_simp
  ring

/-- `Q(q) = 0`, since `Ψ(ξ⋆) = 0` and `ξ⋆ = 1/(1 + q)`. -/
theorem quartic_qStar : quartic qStar = 0 := by
  have hq : 0 < 1 + qStar := by
    rw [one_add_qStar]
    exact one_div_pos.mpr xiStar_pos
  rw [quartic_eq_psi hq, ← xiStar_eq_qStar, xiStar_root.2.2, mul_zero]

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

theorem qStar_lt_one : qStar < 1 := by
  have h := xiStar_root.1
  unfold qStar
  rw [div_lt_one xiStar_pos]
  linarith

/-- The root of `Q` in `[0, 1]` is unique. -/
theorem eq_qStar {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) (hQ : quartic t = 0) : t = qStar :=
  quartic_strictAntiOn.injOn ⟨h₀, h₁⟩ ⟨qStar_pos.le, qStar_lt_one.le⟩ (hQ.trans quartic_qStar.symm)

/-- The bounds (13), from `Q(259/1000) > 0 > Q(13/50)`. -/
theorem qStar_bounds : (259 : ℝ) / 1000 < qStar ∧ qStar < 13 / 50 := by
  have hq := quartic_qStar
  have hmem : qStar ∈ Set.Icc (0 : ℝ) 1 := ⟨qStar_pos.le, qStar_lt_one.le⟩
  constructor
  · by_contra h
    have hle : qStar ≤ 259 / 1000 := le_of_not_gt h
    have hmono := quartic_strictAntiOn.antitoneOn hmem ⟨by norm_num, by norm_num⟩ hle
    have : (0 : ℝ) < quartic (259 / 1000) := by norm_num [quartic]
    linarith
  · by_contra h
    have hle : (13 : ℝ) / 50 ≤ qStar := le_of_not_gt h
    have hmono := quartic_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩ hmem hle
    have : quartic (13 / 50) < (0 : ℝ) := by norm_num [quartic]
    linarith

/-! ### The polynomial `Φ` and the weight `u₁` (Section 2.1) -/

theorem continuous_phi : Continuous phi := by
  unfold phi
  fun_prop

theorem hasDerivAt_phi (x : ℝ) :
    HasDerivAt phi (4 * x ^ 3 + 3 * x ^ 2 - 4 * x - 3) x := by
  have h := ((((hasDerivAt_pow 4 x).add (hasDerivAt_pow 3 x)).sub
    ((hasDerivAt_pow 2 x).const_mul (2 : ℝ))).sub ((hasDerivAt_id x).const_mul (3 : ℝ)))
  convert h.add_const (2 : ℝ) using 1
  norm_num
  ring

/-- `Φ'(x) = (x² - 1)(4x + 3) < 0` on `(0, 1)`, so `Φ` is strictly decreasing on
`[0, 1]`. -/
theorem phi_strictAntiOn : StrictAntiOn phi (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuous_phi.continuousOn
  rw [interior_Icc]
  intro x hx
  rw [(hasDerivAt_phi x).deriv]
  have h : 4 * x ^ 3 + 3 * x ^ 2 - 4 * x - 3 = (x ^ 2 - 1) * (4 * x + 3) := by ring
  rw [h]
  apply mul_neg_of_neg_of_pos _ (by linarith [hx.1])
  nlinarith [hx.1, hx.2]

/-- `Φ(0) = 2 > 0 > -1 = Φ(1)`, so `Φ` has a root in `(0, 1)`. -/
theorem exists_phi_root : ∃ u : ℝ, 0 < u ∧ u < 1 ∧ phi u = 0 := by
  have hsub := intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num) continuous_phi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (phi 1) (phi 0) := by
    constructor <;> norm_num [phi]
  obtain ⟨u, ⟨h0, h1⟩, hu⟩ := hsub hmem
  exact ⟨u, h0, h1, hu⟩

/-- The weight `u₁`, the root of `Φ` in `(0, 1)`. -/
def uOne : ℝ := exists_phi_root.choose

theorem uOne_pos : 0 < uOne := exists_phi_root.choose_spec.1

theorem uOne_lt_one : uOne < 1 := exists_phi_root.choose_spec.2.1

theorem phi_uOne : phi uOne = 0 := exists_phi_root.choose_spec.2.2

/-- The root of `Φ` in `[0, 1]` is unique. -/
theorem eq_uOne {x : ℝ} (h₀ : 0 ≤ x) (h₁ : x ≤ 1) (hx : phi x = 0) : x = uOne :=
  phi_strictAntiOn.injOn ⟨h₀, h₁⟩ ⟨uOne_pos.le, uOne_lt_one.le⟩ (hx.trans phi_uOne.symm)

/-- `1/2 < u₁ < 3/5`, from `Φ(1/2) > 0 > Φ(3/5)`. -/
theorem uOne_bounds : (1 : ℝ) / 2 < uOne ∧ uOne < 3 / 5 := by
  have hmem : uOne ∈ Set.Icc (0 : ℝ) 1 := ⟨uOne_pos.le, uOne_lt_one.le⟩
  constructor
  · by_contra h
    have hle : uOne ≤ 1 / 2 := le_of_not_gt h
    have hmono := phi_strictAntiOn.antitoneOn hmem ⟨by norm_num, by norm_num⟩ hle
    have : (0 : ℝ) < phi (1 / 2) := by norm_num [phi]
    linarith [phi_uOne]
  · by_contra h
    have hle : (3 : ℝ) / 5 ≤ uOne := le_of_not_gt h
    have hmono := phi_strictAntiOn.antitoneOn ⟨by norm_num, by norm_num⟩ hmem hle
    have : phi (3 / 5) < (0 : ℝ) := by norm_num [phi]
    linarith [phi_uOne]

/-- The identity `Q(2u² + 3u - 2) = Φ(u) (16u⁴ + 80u³ + 112u² + 60u + 59)` used in the
proof of Lemma 4. -/
theorem quartic_comp (u : ℝ) :
    quartic (2 * u ^ 2 + 3 * u - 2) =
      phi u * (16 * u ^ 4 + 80 * u ^ 3 + 112 * u ^ 2 + 60 * u + 59) := by
  unfold quartic phi
  ring

/-- `q = u₁ u₂ = u₁³ (1 + u₁)`: with `Φ(u₁) = 0`, `u₁³ (1 + u₁) = 2u₁² + 3u₁ - 2` is
a root of `Q` in `(0, 1)`. -/
theorem qStar_eq_uOne : qStar = uOne ^ 3 * (1 + uOne) := by
  have hu := uOne_bounds
  have hphi := phi_uOne
  have hlin : uOne ^ 3 * (1 + uOne) = 2 * uOne ^ 2 + 3 * uOne - 2 := by
    unfold phi at hphi
    linear_combination hphi
  have hQ : quartic (uOne ^ 3 * (1 + uOne)) = 0 := by
    rw [hlin, quartic_comp, phi_uOne, zero_mul]
  have h0 : 0 ≤ uOne ^ 3 * (1 + uOne) :=
    mul_nonneg (pow_nonneg uOne_pos.le 3) (by linarith [uOne_pos])
  have h1 : uOne ^ 3 * (1 + uOne) ≤ 1 := by
    have h3 : uOne ^ 3 ≤ (3 / 5) ^ 3 := pow_le_pow_left₀ uOne_pos.le hu.2.le 3
    nlinarith
  exact (eq_qStar h0 h1 hQ).symm

/-- `ξ⋆ = 1 / (1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. -/
theorem xiStar_eq_uOne : xiStar = 1 / (1 + uOne ^ 3 * (1 + uOne)) := by
  rw [xiStar_eq_qStar, qStar_eq_uOne]

/-- The constants of the hard instance in Section 2.1 and Appendix A.2: `u₁ ∈ (0, 1)` is
a root of `Φ`, and `ξ⋆ = 1/(1 + u₁ u₂)` with `u₂ = u₁² (1 + u₁)`. -/
theorem exists_hardConstants : ∃ u₁ : ℝ, 0 < u₁ ∧ u₁ < 1 ∧ phi u₁ = 0 ∧
    xiStar = 1 / (1 + u₁ ^ 3 * (1 + u₁)) :=
  ⟨uOne, uOne_pos, uOne_lt_one, phi_uOne, xiStar_eq_uOne⟩

end ConsistentSubmodular.Chains
