module

public import ConsistentSubmodular.Deterministic.Certificates.AtomicProfiles
public import ConsistentSubmodular.Deterministic.Basic.Simplex
public import ConsistentSubmodular.Deterministic.Basic.FiniteExpectation

@[expose] public section

/-! Elementary finite-sum facts for the triangular atomic model. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

theorem supportCard_vertex (i : Fin (m + 1)) : supportCard (vertex i) = 1 := by
  classical
  unfold supportCard
  have h : (Finset.univ.filter (fun j => vertex i j ≠ 0)) = {i} := by
    ext j
    simp [vertex]
  rw [h]
  simp

theorem supportCard_mix_vertices (i j : Fin (m + 1)) (x : ℝ) :
    supportCard (mix (vertex i) (vertex j) x) ≤ 2 := by
  classical
  apply le_trans (Finset.card_le_card (t := {i, j}) ?_)
  · exact le_trans (Finset.card_insert_le i {j}) (by simp)
  · intro k hk
    by_contra h
    have hki : k ≠ i := fun hk => h (by simp [hk])
    have hkj : k ≠ j := fun hk => h (by simp [hk])
    have := (Finset.mem_filter.mp hk).2
    exact this (by simp [mix, vertex, hki, hkj])

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

theorem baseline_nonnegative (t : Fin (m + 1)) : 0 ≤ P.baseline t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> linarith [P.weight_nonnegative a]

theorem residual_nonnegative (i t : Fin (m + 1)) : 0 ≤ P.residual i t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> linarith [P.weight_nonnegative a]

theorem designated_nonnegative (t : Fin (m + 1)) : 0 ≤ P.designated t :=
  P.residual_nonnegative t t

theorem benchmark_nonnegative (t : Fin (m + 1)) : 0 ≤ P.benchmark t :=
  add_nonneg (P.baseline_nonnegative t) (P.designated_nonnegative t)

@[simp] theorem baseline_zero : P.baseline 0 = 0 := by
  simp [baseline]

theorem baseline_monotone : Monotone P.baseline := by
  intro s t hst
  unfold baseline
  apply Finset.sum_le_sum
  intro a _
  by_cases hs : P.pool a < s
  · simp [hs, lt_of_lt_of_le hs hst]
  · simp only [hs, ite_false]
    split_ifs <;> linarith [P.weight_nonnegative a]

theorem residual_antitone (i : Fin (m + 1)) : Antitone (P.residual i) := by
  intro s t hst
  unfold residual
  apply Finset.sum_le_sum
  intro a _
  by_cases ht : t ≤ P.pool a ∧ i ∈ P.labels a
  · simp [ht, le_trans hst ht.1]
  · simp only [ht, ite_false]
    split_ifs <;> linarith [P.weight_nonnegative a]

theorem residual_persistence (i t : Fin (m + 1)) (hti : t ≤ i) :
    P.residual i t = P.designated i := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ P.labels a
  · have hip := P.triangular a i hi
    simp [hi, hip, le_trans hti hip]
  · simp [hi]

theorem baseline_add_residual_monotone (i : Fin (m + 1)) :
    Monotone (fun t => P.baseline t + P.residual i t) := by
  intro s t hst
  simp only [baseline, residual, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw := P.weight_nonnegative a
  by_cases hs : P.pool a < s
  · have ht := lt_of_lt_of_le hs hst
    simp [hs, ht, not_le.mpr hs, not_le.mpr ht]
  · by_cases ht : P.pool a < t
    · simp only [hs, ht, if_false, if_true, not_le.mpr ht, false_and,
        zero_add, add_zero]
      split_ifs <;> linarith
    · have hsp : s ≤ P.pool a := le_of_not_gt hs
      have htp : t ≤ P.pool a := le_of_not_gt ht
      simp [hs, ht, hsp, htp]

theorem designated_antitone (hP : P.Canonical) : Antitone P.designated := by
  intro s t hst
  rw [← P.residual_persistence t s hst]
  exact hP.2 s t

theorem designated_le_one (hP : P.Canonical) (t : Fin (m + 1)) :
    P.designated t ≤ 1 := by
  rw [← hP.1]
  exact P.designated_antitone hP (Fin.zero_le t)

theorem benchmark_monotone (hP : P.Canonical) : Monotone P.benchmark := by
  intro s t hst
  calc
    P.benchmark s = P.baseline s + P.residual s s := rfl
    _ ≤ P.baseline t + P.residual s t := P.baseline_add_residual_monotone s hst
    _ ≤ P.baseline t + P.designated t := add_le_add_right (hP.2 t s) _

theorem benchmark_zero (hP : P.Canonical) : P.benchmark 0 = 1 := by
  simp [benchmark, hP.1]

theorem one_le_benchmark (hP : P.Canonical) (t : Fin (m + 1)) :
    1 ≤ P.benchmark t := by
  rw [← P.benchmark_zero hP]
  exact P.benchmark_monotone hP (Fin.zero_le t)

theorem value_vertex (t i : Fin (m + 1)) :
    P.value t (vertex i) = P.baseline t + P.residual i t := by
  unfold value residual
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [prod_vertex_complement]
  by_cases ht : t ≤ P.pool a <;> by_cases hi : i ∈ P.labels a <;> simp [ht, hi]

theorem value_designated_vertex (t : Fin (m + 1)) :
    P.value t (vertex t) = P.benchmark t := P.value_vertex t t

theorem baseline_le_value (t : Fin (m + 1)) {p : Point m} (hp : IsSimplex p) :
    P.baseline t ≤ P.value t p := by
  apply le_add_of_nonneg_right
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · apply mul_nonneg (P.weight_nonnegative a)
    apply sub_nonneg.mpr
    apply Finset.prod_le_one
    · intro i _
      exact sub_nonneg.mpr (hp.coordinate_le_one i)
    · intro i _
      exact sub_le_self _ (hp.1 i)
  · exact le_rfl

theorem inactive_stage_safe (t : Fin (m + 1)) {p : Point m} (hp : IsSimplex p)
    (ht : 3 * P.designated t ≤ P.baseline t) :
    (3 : ℝ) / 4 * P.benchmark t ≤ P.value t p := by
  have hb := P.baseline_le_value t hp
  unfold benchmark
  linarith

theorem active_is_prefix (hP : P.Canonical) {s t : Fin (m + 1)} (hst : s ≤ t)
    (ht : P.baseline t < 3 * P.designated t) :
    P.baseline s < 3 * P.designated s := by
  have hb := P.baseline_monotone hst
  have hg := P.designated_antitone hP hst
  linarith

def overlap (i j t : Fin (m + 1)) : ℝ :=
  ∑ a, if t ≤ P.pool a ∧ i ∈ P.labels a ∧ j ∈ P.labels a then P.weight a else 0

theorem overlap_nonnegative (i j t : Fin (m + 1)) : 0 ≤ P.overlap i j t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs <;> linarith [P.weight_nonnegative a]

theorem overlap_comm (i j t : Fin (m + 1)) : P.overlap i j t = P.overlap j i t := by
  simp [overlap, and_comm]

theorem overlap_le_left (i j t : Fin (m + 1)) : P.overlap i j t ≤ P.residual i t := by
  unfold overlap residual
  apply Finset.sum_le_sum
  intro a _
  by_cases h : t ≤ P.pool a ∧ i ∈ P.labels a ∧ j ∈ P.labels a
  · simp [h.1, h.2.1, h.2.2]
  · simp only [h, ite_false]
    split_ifs <;> linarith [P.weight_nonnegative a]

theorem overlap_le_right (i j t : Fin (m + 1)) : P.overlap i j t ≤ P.residual j t := by
  rw [P.overlap_comm]
  exact P.overlap_le_left j i t

theorem overlap_le_persistent (i j t : Fin (m + 1)) :
    P.overlap i j t ≤ P.residual i j := by
  unfold overlap residual
  apply Finset.sum_le_sum
  intro a _
  by_cases h : t ≤ P.pool a ∧ i ∈ P.labels a ∧ j ∈ P.labels a
  · have hjp := P.triangular a j h.2.2
    simp [h.1, h.2.1, h.2.2, hjp]
  · simp only [h, ite_false]
    split_ifs <;> linarith [P.weight_nonnegative a]

theorem value_mix_vertices (t i j : Fin (m + 1)) (hij : i ≠ j) (x : ℝ) :
    P.value t (mix (vertex i) (vertex j) x) =
      P.baseline t + (1 - x) * P.residual i t + x * P.residual j t -
        x * (1 - x) * P.overlap i j t := by
  have hsum : (∑ a, if t ≤ P.pool a then
      P.weight a * (1 - ∏ k ∈ P.labels a, (1 - mix (vertex i) (vertex j) x k)) else 0) =
      ∑ a, ((1 - x) * (if t ≤ P.pool a ∧ i ∈ P.labels a then P.weight a else 0) +
        x * (if t ≤ P.pool a ∧ j ∈ P.labels a then P.weight a else 0) -
        x * (1 - x) * (if t ≤ P.pool a ∧ i ∈ P.labels a ∧ j ∈ P.labels a
          then P.weight a else 0)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [prod_mix_vertices_complement _ i j hij]
    by_cases ht : t ≤ P.pool a <;> by_cases hi : i ∈ P.labels a <;>
      by_cases hj : j ∈ P.labels a <;> simp [ht, hi, hj] <;> ring
  unfold value
  rw [hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    residual, overlap]
  ring

theorem value_mix_vertices_lower (t i j : Fin (m + 1)) (hij : i ≠ j)
    {x O : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) (hO : P.overlap i j t ≤ O) :
    P.baseline t + (1 - x) * P.residual i t + x * P.residual j t - x * (1 - x) * O ≤
      P.value t (mix (vertex i) (vertex j) x) := by
  rw [P.value_mix_vertices t i j hij]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hO
    (mul_nonneg hx (sub_nonneg.mpr hx'))) _

theorem value_mix_vertices_sufficient (t i j : Fin (m + 1)) (hij : i ≠ j)
    {x O : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) (hO : P.overlap i j t ≤ O) :
    P.baseline t + (1 - x) * P.residual i t + x * P.residual j t - O / 4 ≤
      P.value t (mix (vertex i) (vertex j) x) := by
  have hOnonneg := (P.overlap_nonnegative i j t).trans hO
  have hquad : x * (1 - x) ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hmul := mul_le_mul_of_nonneg_right hquad hOnonneg
  have hv := P.value_mix_vertices_lower t i j hij hx hx' hO
  nlinarith

theorem terminal_designated : P.designated (Fin.last m) =
    ∑ a, if Fin.last m ≤ P.pool a then P.weight a else 0 := by
  unfold designated residual
  apply Finset.sum_congr rfl
  intro a _
  by_cases hlive : Fin.last m ≤ P.pool a
  · have heq : P.pool a = Fin.last m := le_antisymm (Fin.le_last _) hlive
    by_cases hw : 0 < P.weight a
    · simp [hlive, P.terminal a hw heq]
    · have hz : P.weight a = 0 := le_antisymm (le_of_not_gt hw) (P.weight_nonnegative a)
      simp [hz]
  · simp [hlive]

theorem terminal_overlap_left (i : Fin (m + 1)) :
    P.overlap i (Fin.last m) (Fin.last m) = P.residual i (Fin.last m) := by
  unfold overlap residual
  apply Finset.sum_congr rfl
  intro a _
  by_cases hlive : Fin.last m ≤ P.pool a
  · have heq : P.pool a = Fin.last m := le_antisymm (Fin.le_last _) hlive
    by_cases hw : 0 < P.weight a
    · simp [hlive, P.terminal a hw heq]
    · have hz : P.weight a = 0 := le_antisymm (le_of_not_gt hw) (P.weight_nonnegative a)
      simp [hz]
  · simp [hlive]

theorem terminal_overlap_lower_bound (i j : Fin (m + 1)) :
    P.residual i (Fin.last m) + P.residual j (Fin.last m) -
      P.designated (Fin.last m) ≤ P.overlap i j (Fin.last m) := by
  rw [P.terminal_designated]
  simp only [residual, overlap, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases ht : Fin.last m ≤ P.pool a <;> by_cases hi : i ∈ P.labels a <;>
    by_cases hj : j ∈ P.labels a <;> simp [ht, hi, hj]
  linarith [P.weight_nonnegative a]

theorem value_terminal_edge (i : Fin (m + 1)) (hi : i ≠ Fin.last m) (x : ℝ) :
    P.value (Fin.last m) (mix (vertex i) (vertex (Fin.last m)) x) =
      P.baseline (Fin.last m) + (1 - x) ^ 2 * P.residual i (Fin.last m) +
        x * P.designated (Fin.last m) := by
  rw [P.value_mix_vertices _ _ _ hi, P.terminal_overlap_left]
  unfold designated
  ring

theorem terminal_persistence_budget (hP : P.Canonical) (i : Fin (m + 1)) :
    P.designated (Fin.last m) ≤ P.baseline (Fin.last m) + P.residual i (Fin.last m) := by
  have hi : i ≤ Fin.last m := Fin.le_last i
  have hmono := P.baseline_add_residual_monotone i hi
  have hg := P.designated_antitone hP hi
  have hb := P.baseline_nonnegative i
  change P.baseline i + P.designated i ≤ _ at hmono
  linarith

end AtomicProfile
/-! ### Atomic values as finite independent expectations -/

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

def unionValue (t : Fin (m + 1)) (I : Finset (Fin (m + 1))) : ℝ :=
  P.baseline t + ∑ a, if t ≤ P.pool a ∧ (P.labels a ∩ I).Nonempty then P.weight a else 0

/-- The atomic polynomial is exactly its finite independent type expectation. -/
theorem value_eq_expectation (t : Fin (m + 1)) (p : Point m) :
    P.value t p = finiteExpectation p (P.unionValue t) := by
  unfold unionValue
  rw [finiteExpectation_add, finiteExpectation_const, finiteExpectation_sum]
  unfold value
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : t ≤ P.pool a
  · simp only [ha, true_and, ite_true]
    exact (finiteExpectation_weighted_hit p (P.labels a) (P.weight a)).symm
  · simp only [ha, false_and, ite_false, finiteExpectation_const]

end AtomicProfile

end ConsistentSubmodular
