module

public import ConsistentSubmodular.Deterministic.Reduction.PhysicalOperationPath

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace Objective
variable {n : ℕ} (f : Objective n)

theorem exists_insertion_first_bridge (A B Q : Finset (Fin n)) (V : ℝ)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧
      P.length ≤ A.card + B.card ∧ ∀ j, P.node j ⊆ A ∪ B ∧
        (P.node j).card ≤ A.card + B.card ∧ V ≤ f.value (Q ∪ P.node j) := by
  obtain ⟨L, hLl, hL0, hL1, hL⟩ := SetOperationPath.exists_insertion_path A B
  obtain ⟨R, hRl, hR0, hR1, hR⟩ := SetOperationPath.exists_insertion_path B A
  have hj : L.node L.length = R.reverse.node 0 := by
    rw [SetOperationPath.reverse_initial, hL1, hR1, Finset.union_comm]
  refine ⟨L.append R.reverse hj, by simpa using hL0, ?_, ?_, ?_⟩
  · simpa using (L.append_terminal R.reverse hj).trans (by simpa [SetOperationPath.reverse] using hR0)
  · simp only [SetOperationPath.append_length, SetOperationPath.reverse]
    omega
  · apply L.append_property R.reverse hj
      (fun S => S ⊆ A ∪ B ∧ S.card ≤ A.card + B.card ∧ V ≤ f.value (Q ∪ S))
    · intro j
      refine ⟨(hL j).2, (Finset.card_le_card (hL j).2).trans (Finset.card_union_le _ _), ?_⟩
      exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right (hL j).1))
    · intro j
      have hs : R.reverse.node j ⊆ A ∪ B := by simpa [SetOperationPath.reverse, Finset.union_comm] using (hR (R.length - j)).2
      refine ⟨hs, (Finset.card_le_card hs).trans (Finset.card_union_le _ _), ?_⟩
      exact hB.trans (f.monotone _ _ (Finset.union_subset_union_right (hR (R.length - j)).1))

theorem exists_zero_bridge (A B Q : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧
      P.length ≤ A.card + B.card ∧ ∀ j, P.node j ⊆ A ∪ B ∧
        (P.node j).card ≤ max A.card B.card ∧ 0 ≤ f.value (Q ∪ P.node j) := by
  obtain ⟨P, hl, h0, h1, hn⟩ := SetOperationPath.exists_deletion_first A B
  refine ⟨P, h0, h1, ?_, fun j => ⟨(hn j).2.1, (hn j).2.2, f.nonnegative _⟩⟩
  rw [hl]
  unfold recourse
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset))

end Objective
end ConsistentSubmodular
