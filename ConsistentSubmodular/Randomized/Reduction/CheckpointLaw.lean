module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# Finite laws for the checkpoint algorithm

The randomness of Algorithm 1 (Appendix A.3) consists of one sample per
checkpoint and one uniformly random subblock per block, all independent. This
file provides finite probability laws, their products, the marginals that the
proof of Lemma 1 uses, and the law of the resulting trajectory as a
`RandomTrajectory`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

/-- A probability law on a finite type: nonnegative weights summing to one. -/
structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  sum_one : ∑ ω, weight ω = 1

namespace Law

variable {Ω : Type*} [Fintype Ω]

/-- The expectation `E[X]`. -/
def expect (μ : Law Ω) (X : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * X ω

theorem expect_mono (μ : Law Ω) {X Y : Ω → ℝ} (h : ∀ ω, μ.weight ω ≠ 0 → X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : μ.weight ω = 0
  · simp [hω]
  · exact mul_le_mul_of_nonneg_left (h ω hω) (μ.nonneg ω)

theorem expect_add (μ : Law Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_const (μ : Law Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.sum_one, one_mul]

theorem expect_nonneg (μ : Law Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (h ω)

/-- The point mass at `ω₀`. -/
def dirac [DecidableEq Ω] (ω₀ : Ω) : Law Ω where
  weight ω := if ω = ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_one := by simp

theorem expect_dirac [DecidableEq Ω] (ω₀ : Ω) (X : Ω → ℝ) :
    (dirac ω₀).expect X = X ω₀ := by
  simp [expect, dirac]

/-- The uniform law on `Fin h`, for `h ≥ 1`. -/
def uniform (h : ℕ) (hh : 0 < h) : Law (Fin h) where
  weight _ := 1 / h
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

theorem expect_uniform (h : ℕ) (hh : 0 < h) (X : Fin h → ℝ) :
    (uniform h hh).expect X = (∑ i, X i) / h := by
  simp only [expect, uniform, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Independent coordinates: the product of laws `μ i` on `X`, indexed by a
finite type `ι`. -/
def pi {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] (μ : ι → Law X) :
    Law (ι → X) where
  weight x := ∏ i, (μ i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (μ i).nonneg (x i)
  sum_one := by
    rw [← Fintype.prod_sum (fun i a => (μ i).weight a)]
    simp only [(μ _).sum_one, Finset.prod_const_one]

/-- The marginal of one coordinate of a product law. -/
theorem expect_pi_apply {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) (i : ι) (F : X → ℝ) :
    (pi μ).expect (fun x => F (x i)) = (μ i).expect F := by
  let g : ι → X → ℝ := fun j a => (μ j).weight a * if j = i then F a else 1
  have hpoint (x : ι → X) : (∏ j, (μ j).weight (x j)) * F (x i) = ∏ j, g j (x j) := by
    simp only [g, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
  have hrow (j : ι) : ∑ a, g j a = if j = i then (μ i).expect F else 1 := by
    by_cases hji : j = i
    · subst hji
      simp [g, expect]
    · simp [g, hji, (μ j).sum_one]
  calc (pi μ).expect (fun x => F (x i))
      = ∑ x : ι → X, ∏ j, g j (x j) := by
        simp only [expect, pi]
        exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = ∏ j, ∑ a, g j a := (Fintype.prod_sum g).symm
    _ = (μ i).expect F := by
        simp only [hrow, Finset.prod_ite_eq', Finset.mem_univ, if_true]

/-- Weights of a product law vanish unless every coordinate has positive weight. -/
theorem weight_pi_ne_zero {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X]
    (μ : ι → Law X) {x : ι → X} (hx : (pi μ).weight x ≠ 0) (i : ι) :
    (μ i).weight (x i) ≠ 0 := by
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

variable {Y : Type*} [Fintype Y]

/-- Two independent components. -/
def prod (μ : Law Ω) (ν : Law Y) : Law (Ω × Y) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  sum_one := by
    rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, μ.sum_one, ν.sum_one, one_mul]

theorem expect_prod_mul (μ : Law Ω) (ν : Law Y) (F : Ω → ℝ) (G : Y → ℝ) :
    (μ.prod ν).expect (fun p => F p.1 * G p.2) = μ.expect F * ν.expect G := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun y _ => by ring

theorem weight_prod_ne_zero (μ : Law Ω) (ν : Law Y) {p : Ω × Y}
    (hp : (μ.prod ν).weight p ≠ 0) : μ.weight p.1 ≠ 0 ∧ ν.weight p.2 ≠ 0 := by
  simp only [prod] at hp
  exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩

/-- The law of the trajectory `τ ω`, the pushforward of `μ` under `τ`. -/
def trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n)) :
    RandomTrajectory n := by
  classical
  exact
    { prob := fun S => ∑ ω ∈ Finset.univ.filter (fun ω => τ ω = S), μ.weight ω
      prob_nonneg := fun S => Finset.sum_nonneg fun ω _ => μ.nonneg ω
      prob_sum := by rw [Finset.sum_fiberwise Finset.univ τ μ.weight]; exact μ.sum_one }

theorem expectation_trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n))
    (g : Finset (Fin n) → ℝ) (t : Fin (n + 1)) :
    (μ.trajectory τ).expectation g t = μ.expect (fun ω => g (τ ω t)) := by
  classical
  unfold RandomTrajectory.expectation trajectory expect
  simp only [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ τ (fun ω => μ.weight ω * g (τ ω t))]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun ω hω => ?_
  rw [(Finset.mem_filter.mp hω).2]

theorem feasible_trajectory (μ : Law Ω) {n : ℕ} (τ : Ω → Fin (n + 1) → Finset (Fin n))
    {k C : ℕ} (h : ∀ ω, μ.weight ω ≠ 0 → FeasibleTrajectory k C (τ ω)) :
    (μ.trajectory τ).Feasible k C := by
  classical
  intro S hS
  obtain ⟨ω, hω, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [← (Finset.mem_filter.mp hω).2]
  exact h ω hne

end Law

end ConsistentSubmodular.Checkpoints
