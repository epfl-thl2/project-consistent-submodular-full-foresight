module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
Elementary facts about the model of Section 1.1: arrived prefixes, recourse,
subadditivity and diminishing returns of objectives, optimal cores with a
fixed buffer, and exact optimal trajectories.

The exact optimal trajectory has recourse `2 k`, which depends on the
instance; it serves only small budgets.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

@[simp] theorem arrivedPrefix_zero (n : ℕ) : arrivedPrefix n 0 = ∅ := by
  simp [arrivedPrefix]

theorem arrivedPrefix_mono {s t : ℕ} (hst : s ≤ t) :
    arrivedPrefix n s ⊆ arrivedPrefix n t := by
  intro e he
  simp only [arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact lt_of_lt_of_le he hst

theorem recourse_le_card_add (A B : Finset (Fin n)) :
    recourse A B ≤ A.card + B.card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_le_card Finset.sdiff_subset)
      (Finset.card_le_card Finset.sdiff_subset))

theorem recourse_le_twice_budget {A B : Finset (Fin n)} {k : ℕ}
    (hA : A.card ≤ k) (hB : B.card ≤ k) : recourse A B ≤ 2 * k := by
  have := recourse_le_card_add A B
  omega

namespace Objective

variable (f : Objective n)

/-- An exact finite optimizer on an arbitrary old ground set and fixed buffer. -/
theorem exists_buffered_optimizer (N Q : Finset (Fin n)) (k : ℕ) :
    ∃ A : Finset (Fin n), A ⊆ N ∧ A.card ≤ k ∧
      ∀ B : Finset (Fin n), B ⊆ N → B.card ≤ k →
        f.value (Q ∪ B) ≤ f.value (Q ∪ A) := by
  classical
  let candidates := N.powerset.filter (fun A => A.card ≤ k)
  have hnonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates]
  obtain ⟨A, hA, hmax⟩ := candidates.exists_max_image
    (fun A => f.value (Q ∪ A)) hnonempty
  simp only [candidates, Finset.mem_filter, Finset.mem_powerset] at hA
  refine ⟨A, hA.1, hA.2, ?_⟩
  intro B hBN hBk
  exact hmax B (by simp [candidates, hBN, hBk])

def bufferedOptimizer (N Q : Finset (Fin n)) (k : ℕ) : Finset (Fin n) :=
  Classical.choose (f.exists_buffered_optimizer N Q k)

theorem bufferedOptimizer_spec (N Q : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimizer N Q k ⊆ N ∧
      (f.bufferedOptimizer N Q k).card ≤ k ∧
      ∀ B : Finset (Fin n), B ⊆ N → B.card ≤ k →
        f.value (Q ∪ B) ≤ f.value (Q ∪ f.bufferedOptimizer N Q k) :=
  Classical.choose_spec (f.exists_buffered_optimizer N Q k)

def bufferedOptimum (N Q : Finset (Fin n)) (k : ℕ) : ℝ :=
  f.value (Q ∪ f.bufferedOptimizer N Q k)

theorem le_bufferedOptimum {N Q A : Finset (Fin n)} {k : ℕ}
    (hAN : A ⊆ N) (hAk : A.card ≤ k) :
    f.value (Q ∪ A) ≤ f.bufferedOptimum N Q k :=
  (f.bufferedOptimizer_spec N Q k).2.2 A hAN hAk

theorem value_le_bufferedOptimum (N Q : Finset (Fin n)) (k : ℕ) :
    f.value Q ≤ f.bufferedOptimum N Q k := by
  simpa using f.le_bufferedOptimum (N := N) (Q := Q) (k := k)
    (Finset.empty_subset N) (Nat.zero_le k)

theorem bufferedOptimum_nonnegative (N Q : Finset (Fin n)) (k : ℕ) :
    0 ≤ f.bufferedOptimum N Q k := f.nonnegative _

theorem union_le (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B - f.value ∅ := by
  have hsub := f.submodular A B
  have hemp := f.monotone ∅ (A ∩ B) (Finset.empty_subset _)
  linarith

theorem subadditive (A B : Finset (Fin n)) :
    f.value (A ∪ B) ≤ f.value A + f.value B := by
  have h := f.union_le A B
  have h0 := f.nonnegative ∅
  linarith

/-- Setwise diminishing returns, including overlapping increments. -/
theorem diminishing_returns {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (E : Finset (Fin n)) :
    f.value (B ∪ E) - f.value B ≤ f.value (A ∪ E) - f.value A := by
  have hs := f.submodular B (A ∪ E)
  have hbase := f.monotone A (B ∩ (A ∪ E)) (by
    intro e he
    exact Finset.mem_inter.mpr ⟨hAB he, Finset.mem_union_left E he⟩)
  have hU : B ∪ (A ∪ E) = B ∪ E := by
    ext e
    simp only [Finset.mem_union]
    constructor
    · rintro (he | he | he)
      · exact Or.inl he
      · exact Or.inl (hAB he)
      · exact Or.inr he
    · rintro (he | he)
      · exact Or.inl he
      · exact Or.inr (Or.inr he)
  rw [hU] at hs
  linarith

theorem bufferedOptimum_mono {N Q R : Finset (Fin n)} {k : ℕ}
    (hQR : Q ⊆ R) : f.bufferedOptimum N Q k ≤ f.bufferedOptimum N R k := by
  have hA := f.bufferedOptimizer_spec N Q k
  exact (f.monotone _ _ (Finset.union_subset_union_left hQR)).trans
    (f.le_bufferedOptimum hA.1 hA.2.1)

/-- A window optimum cannot grow faster than its increasing buffer. -/
theorem bufferedOptimum_growth {N Q R : Finset (Fin n)} {k : ℕ}
    (hQR : Q ⊆ R) :
    f.bufferedOptimum N R k - f.bufferedOptimum N Q k ≤
      f.value R - f.value Q := by
  let A := f.bufferedOptimizer N R k
  have hA := f.bufferedOptimizer_spec N R k
  have hdr := f.diminishing_returns hQR A
  have hmax : f.value (Q ∪ A) ≤ f.bufferedOptimum N Q k :=
    f.le_bufferedOptimum hA.1 hA.2.1
  change f.value (R ∪ A) - f.bufferedOptimum N Q k ≤ _
  linarith

theorem bufferedOptimum_le (N Q : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum N Q k ≤
      f.value Q + f.bufferedOptimum N ∅ k - f.value ∅ := by
  have hA := f.bufferedOptimizer_spec N Q k
  have hmax : f.value (f.bufferedOptimizer N Q k) ≤ f.bufferedOptimum N ∅ k := by
    simpa using f.le_bufferedOptimum (Q := ∅) hA.1 hA.2.1
  have hu := f.union_le Q (f.bufferedOptimizer N Q k)
  change f.value (Q ∪ f.bufferedOptimizer N Q k) ≤ _
  linarith

/-- Zero old scale needs neither normalization nor nonempty old cores. -/
theorem bufferedOptimum_eq_of_zero_scale {N : Finset (Fin n)} {k : ℕ}
    (hzero : f.bufferedOptimum N ∅ k = 0) (Q : Finset (Fin n)) :
    f.bufferedOptimum N Q k = f.value Q := by
  have hu := f.bufferedOptimum_le N Q k
  have hl := f.value_le_bufferedOptimum N Q k
  have h0 := f.nonnegative ∅
  rw [hzero] at hu
  linarith

def exactTrajectory (k : ℕ) (t : Fin (n + 1)) : Finset (Fin n) :=
  f.bufferedOptimizer (arrivedPrefix n t.val) ∅ k

theorem exactTrajectory_feasible (k : ℕ) :
    FeasibleTrajectory k (2 * k) (f.exactTrajectory k) := by
  have hspec : ∀ t : Fin (n + 1),
      f.exactTrajectory k t ⊆ arrivedPrefix n t.val ∧
      (f.exactTrajectory k t).card ≤ k := by
    intro t
    exact ⟨(f.bufferedOptimizer_spec _ _ _).1,
      (f.bufferedOptimizer_spec _ _ _).2.1⟩
  refine ⟨?_, hspec, ?_⟩
  · exact Finset.subset_empty.mp (by simpa using (hspec 0).1)
  · intro t
    exact recourse_le_twice_budget (hspec t.succ).2 (hspec t.castSucc).2

theorem exactTrajectory_optimal (k : ℕ) (t : Fin (n + 1))
    (A : Finset (Fin n)) (hA : A ⊆ arrivedPrefix n t.val) (hk : A.card ≤ k) :
    f.value A ≤ f.value (f.exactTrajectory k t) := by
  simpa [exactTrajectory] using
    (f.bufferedOptimizer_spec (arrivedPrefix n t.val) ∅ k).2.2 A hA hk

theorem exists_exact_trajectory (k : ℕ) :
    ∃ S : Fin (n + 1) → Finset (Fin n),
      FeasibleTrajectory k (2 * k) S ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k → f.value A ≤ f.value (S t) :=
  ⟨f.exactTrajectory k, f.exactTrajectory_feasible k, f.exactTrajectory_optimal k⟩

end Objective

/-- The small-capacity branch has a uniform bound once `K` is fixed. -/
theorem small_budget_trajectory (K k : ℕ) (hk : k ≤ K)
    (f : Objective n) {α : ℝ} (hα : α ≤ 1) :
    ∃ S : Fin (n + 1) → Finset (Fin n), FeasibleTrajectory k (2 * K) S ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k → α * f.value A ≤ f.value (S t) := by
  obtain ⟨S, hS, hopt⟩ := f.exists_exact_trajectory k
  refine ⟨S, ⟨hS.1, hS.2.1, ?_⟩, ?_⟩
  · intro t
    exact (hS.2.2 t).trans (Nat.mul_le_mul_left 2 hk)
  · intro t A hA hAk
    exact (mul_le_of_le_one_left (f.nonnegative A) hα).trans (hopt t A hA hAk)

end ConsistentSubmodular
