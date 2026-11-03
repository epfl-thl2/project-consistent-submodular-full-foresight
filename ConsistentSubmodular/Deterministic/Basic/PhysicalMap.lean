module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-! The linear map from type probabilities to physical element probabilities.
These finite identities allow overlapping and identical cores. The multilinear
domination theorem is in `PhysicalSampling`. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {n m : ℕ}

def physicalProbability (cores : Fin (m + 1) → Finset (Fin n))
    (p : Point m) (e : Fin n) : ℝ :=
  ∑ i, if e ∈ cores i then p i else 0

theorem physicalProbability_nonnegative
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) : 0 ≤ physicalProbability cores p e := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · rfl

theorem physicalProbability_le_mass
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (e : Fin n) :
    physicalProbability cores p e ≤ ∑ i, p i := by
  exact Finset.sum_le_sum (fun i _ => by split_ifs <;> simp_all)

theorem physicalProbability_mem_unitInterval
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : IsSimplex p) (e : Fin n) :
    0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
  exact ⟨physicalProbability_nonnegative cores p hp.1 e,
    (physicalProbability_le_mass cores p hp.1 e).trans_eq hp.2⟩

theorem physicalProbability_total
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m) :
    (∑ e, physicalProbability cores p e) = ∑ i, p i * (cores i).card := by
  unfold physicalProbability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm]

theorem physicalProbability_total_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, physicalProbability cores p e) ≤ k := by
  rw [physicalProbability_total]
  calc
    (∑ i, p i * (cores i).card) ≤ ∑ i, p i * (k : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (hp i))
    _ = (∑ i, p i) * k := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * (k : ℝ) := mul_le_mul_of_nonneg_right hmass (Nat.cast_nonneg k)
    _ = k := one_mul _

theorem physicalProbability_vertex
    (cores : Fin (m + 1) → Finset (Fin n)) (i : Fin (m + 1)) (e : Fin n) :
    physicalProbability cores (vertex i) e = if e ∈ cores i then 1 else 0 := by
  classical
  unfold physicalProbability vertex
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Adjacent shared-threshold intersections dominate the physical image of
the coordinatewise minimum, even for overlapping cores. -/
theorem physicalProbability_min_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    physicalProbability cores (fun i => min (p i) (q i)) e ≤
      min (physicalProbability cores p e) (physicalProbability cores q e) := by
  apply le_min
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact min_le_left _ _
    · rfl
  · apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact min_le_right _ _
    · rfl

theorem physicalProbability_abs_difference_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    |physicalProbability cores p e - physicalProbability cores q e| ≤
      physicalProbability cores (fun i => |p i - q i|) e := by
  unfold physicalProbability
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> simp

/-- Expected changes along a shared-threshold transition are bounded by the
type L1 distance times core capacity, with repeated physical elements counted
only once in the actual recourse. -/
theorem physicalProbability_l1_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m)
    {k : ℕ} (hcore : ∀ i, (cores i).card ≤ k) :
    (∑ e, |physicalProbability cores p e - physicalProbability cores q e|) ≤
      (k : ℝ) * ∑ i, |p i - q i| := by
  calc
    _ ≤ ∑ e, physicalProbability cores (fun i => |p i - q i|) e :=
      Finset.sum_le_sum (fun e _ => physicalProbability_abs_difference_le cores p q e)
    _ = ∑ i, |p i - q i| * (cores i).card := physicalProbability_total _ _
    _ ≤ ∑ i, |p i - q i| * (k : ℝ) := Finset.sum_le_sum
      (fun i _ => mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcore i)) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ConsistentSubmodular
