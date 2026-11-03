module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-! Elementary facts about points of the simplex `Δ` and segments between them. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {m : ℕ}

@[simp] theorem mix_zero (p q : Point m) : mix p q 0 = p := by
  funext i
  simp [mix]

@[simp] theorem mix_one (p q : Point m) : mix p q 1 = q := by
  funext i
  simp [mix]

@[simp] theorem mix_self (p : Point m) (x : ℝ) : mix p p x = p := by
  funext i
  simp only [mix]
  ring

theorem mix_swap (p q : Point m) (x : ℝ) : mix p q x = mix q p (1 - x) := by
  funext i
  simp only [mix]
  ring

theorem mix_mix_left (p q : Point m) (x y : ℝ) :
    mix (mix p q x) p y = mix p q ((1 - y) * x) := by
  funext i
  simp only [mix]
  ring

theorem mix_mix_right (p q : Point m) (x y : ℝ) :
    mix (mix p q x) q y = mix p q ((1 - y) * x + y) := by
  funext i
  simp only [mix]
  ring

theorem mix_mix (p q : Point m) (a b x : ℝ) :
    mix (mix p q a) (mix p q b) x = mix p q ((1 - x) * a + x * b) := by
  funext i
  simp only [mix]
  ring

theorem simplex_vertex (i : Fin (m + 1)) : IsSimplex (vertex i) := by
  constructor
  · intro j
    simp only [vertex]
    split_ifs <;> norm_num
  · simp [vertex]

theorem IsSimplex.coordinate_le_one {p : Point m} (hp : IsSimplex p)
    (i : Fin (m + 1)) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

theorem IsSimplex.mix {p q : Point m} (hp : IsSimplex p) (hq : IsSimplex q)
    {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) : IsSimplex (mix p q x) := by
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hx') (hp.1 i))
      (mul_nonneg hx (hq.1 i))
  · change (∑ i, ((1 - x) * p i + x * q i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hq.2]
    ring

theorem prod_vertex_complement (s : Finset (Fin (m + 1))) (i : Fin (m + 1)) :
    (∏ j ∈ s, (1 - vertex i j)) = if i ∈ s then 0 else 1 := by
  classical
  by_cases hi : i ∈ s
  · simp only [hi, if_pos]
    exact Finset.prod_eq_zero hi (by simp [vertex])
  · simp only [hi, ite_false]
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [vertex, hji]

theorem prod_mix_vertices_complement (s : Finset (Fin (m + 1)))
    (i j : Fin (m + 1)) (hij : i ≠ j) (x : ℝ) :
    (∏ k ∈ s, (1 - mix (vertex i) (vertex j) x k)) =
      (if i ∈ s then x else 1) * (if j ∈ s then 1 - x else 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
      rw [Finset.prod_insert hk, ih]
      by_cases hki : k = i
      · subst k
        simp [mix, vertex, hk, hij, Ne.symm hij]
      · by_cases hkj : k = j
        · subst k
          simp [mix, vertex, hk, hij, Ne.symm hij, mul_comm]
        · simp [mix, vertex, hki, hkj, Ne.symm hki, Ne.symm hkj]

end ConsistentSubmodular
