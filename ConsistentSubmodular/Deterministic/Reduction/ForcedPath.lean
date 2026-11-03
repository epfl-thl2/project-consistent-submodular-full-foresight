module

public import ConsistentSubmodular.Deterministic.Reduction.PhysicalOperationPath

@[expose] public section

/-! Forced elements can be added and removed at pure core endpoints, preserving
all monotone value certificates and a uniform old-ground-set bound. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace SetOperationPath

variable {n : ℕ}

theorem prepend_forced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hstart : P.node 0 = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = D.card + P.length ∧ R.node 0 = A ∧
      R.node R.length = P.node P.length ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : L.node L.length = P.node 0 := by rw [hLterm, hstart, Finset.union_comm]
  refine ⟨L.append P hj, by simp [hLlen], by simpa using hLinit, ?_, ?_⟩
  · exact L.append_terminal P hj
  · apply L.append_property P hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) _ hP
    intro i
    exact ⟨(hLnode i).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode i).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode i).1 hA⟩

theorem append_unforced (P : SetOperationPath n) (A D U : Finset (Fin n))
    (B : ℕ) (good : Finset (Fin n) → Prop)
    (hmono : ∀ S T, S ⊆ T → good S → good T)
    (hend : P.node P.length = D ∪ A) (hA : good A)
    (hAU : A ⊆ U) (hDU : D ⊆ U) (hcard : A.card + D.card ≤ B)
    (hP : ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i)) :
    ∃ R : SetOperationPath n,
      R.length = P.length + D.card ∧ R.node 0 = P.node 0 ∧
      R.node R.length = A ∧
      ∀ i, R.node i ⊆ U ∧ (R.node i).card ≤ B ∧ good (R.node i) := by
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path A D
  have hj : P.node P.length = L.reverse.node 0 := by
    rw [reverse_initial, hLterm, hend, Finset.union_comm]
  refine ⟨P.append L.reverse hj, by simp [reverse, hLlen], by simp, ?_, ?_⟩
  · simpa using (P.append_terminal L.reverse hj).trans ((reverse_terminal L).trans hLinit)
  · apply P.append_property L.reverse hj (fun S => S ⊆ U ∧ S.card ≤ B ∧ good S) hP
    intro i
    exact ⟨(hLnode _).2.trans (Finset.union_subset hAU hDU),
      (Finset.card_le_card (hLnode _).2).trans ((Finset.card_union_le _ _).trans hcard),
      hmono _ _ (hLnode _).1 hA⟩

/-- A `Fin`-indexed sampling sequence has an exact deletion-first realization.
This form directly matches the output of simultaneous threshold rounding. -/
theorem exists_chain_fin {K : ℕ} (S : Fin (K + 1) → Finset (Fin n))
    (B : ℕ) (U : Finset (Fin n)) (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i : Fin K, good (S i.castSucc ∩ S i.succ)) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i : Fin K, recourse (S i.castSucc) (S i.succ) ∧
      P.node 0 = S 0 ∧ P.node P.length = S (Fin.last K) ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by
  let s : ℕ → Finset (Fin n) := fun i => S ⟨min i K, by omega⟩
  have hi (i : ℕ) (hi : i ≤ K) : s i = S ⟨i, by omega⟩ := by simp [s, Nat.min_eq_left hi]
  obtain ⟨P, hlen, hinit, hterm, hP⟩ := exists_chain s K B U good hmono
    (by simpa [s] using hstart)
    (fun i hi' => by rw [hi i hi']; exact hnodes _)
    (fun i hi' => by
      rw [hi i (by omega), hi (i + 1) (by omega)]
      exact hinter ⟨i, hi'⟩)
  refine ⟨P, ?_, ?_, ?_, hP⟩
  · rw [hlen]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hi i.val (by omega), hi (i.val + 1) (by omega)]
    rfl
  · simpa [s] using hinit
  · simpa [s] using hterm

end SetOperationPath
end ConsistentSubmodular
