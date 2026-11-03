module

public import ConsistentSubmodular.Deterministic.Reduction.OperationPath

@[expose] public section

/-! Deletion-first realization of physical changes by single-element operations. -/

noncomputable section
namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_comm (A B : Finset (Fin n)) : recourse A B = recourse B A := by
  simp only [recourse, Finset.union_comm]

namespace SetOperationPath

def oneStep (A B : Finset (Fin n)) (h : recourse B A ≤ 1) : SetOperationPath n where
  length := 1
  node i := if i = 0 then A else B
  stationary i hi := by simp [show i ≠ 0 by omega]
  step i := by
    by_cases hi : i = 0
    · simpa [hi] using h
    · simp [hi, recourse]

def reverse (P : SetOperationPath n) : SetOperationPath n where
  length := P.length
  node i := P.node (P.length - i)
  stationary i hi := by simp [Nat.sub_eq_zero_of_le hi]
  step i := by
    rw [recourse_comm]
    by_cases hi : i < P.length
    · have h := P.step (P.length - (i + 1))
      rw [show P.length - (i + 1) + 1 = P.length - i by omega] at h
      exact h
    · simp [Nat.sub_eq_zero_of_le (show P.length ≤ i by omega),
        Nat.sub_eq_zero_of_le (show P.length ≤ i + 1 by omega), recourse]

@[simp] theorem reverse_initial (P : SetOperationPath n) :
    P.reverse.node 0 = P.node P.length := by simp [reverse]

@[simp] theorem reverse_terminal (P : SetOperationPath n) :
    P.reverse.node P.length = P.node 0 := by simp [reverse]

/-- Insertion of an arbitrary finite list, permitting harmless stuttering when
an inserted element was already present. -/
theorem exists_insertion_path (A C : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = C.card ∧ P.node 0 = A ∧
      P.node P.length = A ∪ C ∧ ∀ i, A ⊆ P.node i ∧ P.node i ⊆ A ∪ C := by
  classical
  induction C using Finset.induction_on with
  | empty =>
    refine ⟨constant A, by rfl, rfl, by simp [constant], ?_⟩
    intro i
    simp [constant]
  | @insert e C he ih =>
    obtain ⟨P, hlen, hinit, hterm, hnode⟩ := ih
    have hs : recourse (insert e (A ∪ C)) (A ∪ C) ≤ 1 := by
      unfold recourse
      have hsub : (insert e (A ∪ C) \ (A ∪ C)) ∪ ((A ∪ C) \ insert e (A ∪ C)) ⊆ {e} := by
        intro x hx
        simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_singleton] at *
        tauto
      exact (Finset.card_le_card hsub).trans (by simp)
    let Q := oneStep (A ∪ C) (insert e (A ∪ C)) hs
    have hj : P.node P.length = Q.node 0 := by simpa [Q, oneStep] using hterm
    refine ⟨P.append Q hj, ?_, ?_, ?_, ?_⟩
    · simp [hlen, Q, oneStep, Finset.card_insert_of_notMem he]
    · simpa using hinit
    · simpa [Q, oneStep, Finset.union_insert] using P.append_terminal Q hj
    · apply P.append_property Q hj (fun S => A ⊆ S ∧ S ⊆ A ∪ insert e C)
      · intro i
        exact ⟨(hnode i).1, (hnode i).2.trans (by intro x hx; simp at *; tauto)⟩
      · intro i
        change A ⊆ (if i = 0 then A ∪ C else insert e (A ∪ C)) ∧
          (if i = 0 then A ∪ C else insert e (A ∪ C)) ⊆ A ∪ insert e C
        split_ifs <;> constructor <;> intro x hx <;> simp at * <;> tauto

/-- Every change of physical sets has a deletion-first realization. Every
intermediate set retains their intersection and uses no more space than the
larger endpoint; its exact operation count is full symmetric difference. -/
theorem exists_deletion_first (A B : Finset (Fin n)) :
    ∃ P : SetOperationPath n, P.length = recourse A B ∧ P.node 0 = A ∧
      P.node P.length = B ∧ ∀ i,
        A ∩ B ⊆ P.node i ∧ P.node i ⊆ A ∪ B ∧
          (P.node i).card ≤ max A.card B.card := by
  classical
  obtain ⟨L, hLlen, hLinit, hLterm, hLnode⟩ := exists_insertion_path (A ∩ B) (A \ B)
  obtain ⟨R, hRlen, hRinit, hRterm, hRnode⟩ := exists_insertion_path (A ∩ B) (B \ A)
  have hleft : (A ∩ B) ∪ (A \ B) = A := by ext x; simp; tauto
  have hright : (A ∩ B) ∪ (B \ A) = B := by ext x; simp; tauto
  rw [hleft] at hLterm hLnode
  rw [hright] at hRterm hRnode
  have hj : L.reverse.node L.reverse.length = R.node 0 := by simpa [reverse] using hLinit.trans hRinit.symm
  have hlen : (L.reverse.append R hj).length = recourse A B := by
    rw [append_length]
    change L.length + R.length = _
    rw [hLlen, hRlen]
    unfold recourse
    exact (Finset.card_union_of_disjoint (by
      apply Finset.disjoint_left.mpr
      intro e heA heB
      exact (Finset.mem_sdiff.mp heA).2 (Finset.mem_sdiff.mp heB).1)).symm
  refine ⟨L.reverse.append R hj, hlen, ?_, ?_, ?_⟩
  · simpa using hLterm
  · simpa using (L.reverse.append_terminal R hj).trans hRterm
  · apply L.reverse.append_property R hj
      (fun S => A ∩ B ⊆ S ∧ S ⊆ A ∪ B ∧ S.card ≤ max A.card B.card)
    · intro i
      exact ⟨(hLnode _).1, (hLnode _).2.trans Finset.subset_union_left,
        (Finset.card_le_card (hLnode _).2).trans (le_max_left _ _)⟩
    · intro i
      exact ⟨(hRnode i).1, (hRnode i).2.trans Finset.subset_union_right,
        (Finset.card_le_card (hRnode i).2).trans (le_max_right _ _)⟩

end SetOperationPath

namespace SetOperationPath

open scoped BigOperators

/-- Concatenate deletion-first changes along an arbitrary finite sequence.
The intersection certificates protect every intermediate operation. -/
theorem exists_chain (S : ℕ → Finset (Fin n)) (m B : ℕ) (U : Finset (Fin n))
    (good : Finset (Fin n) → Prop)
    (hmono : ∀ A B, A ⊆ B → good A → good B)
    (hstart : good (S 0))
    (hnodes : ∀ i, i ≤ m → S i ⊆ U ∧ (S i).card ≤ B)
    (hinter : ∀ i, i < m → good (S i ∩ S (i + 1))) :
    ∃ P : SetOperationPath n,
      P.length = ∑ i ∈ Finset.range m, recourse (S i) (S (i + 1)) ∧
      P.node 0 = S 0 ∧ P.node P.length = S m ∧
      ∀ i, P.node i ⊆ U ∧ (P.node i).card ≤ B ∧ good (P.node i) := by
  induction m with
  | zero =>
    refine ⟨constant (S 0), by simp [constant], rfl, rfl, ?_⟩
    intro i
    exact ⟨(hnodes 0 (by omega)).1, (hnodes 0 (by omega)).2, hstart⟩
  | succ m ih =>
    obtain ⟨P, hlen, hinit, hterm, hnode⟩ := ih
      (fun i hi => hnodes i (by omega)) (fun i hi => hinter i (by omega))
    obtain ⟨Q, hQlen, hQinit, hQterm, hQnode⟩ := exists_deletion_first (S m) (S (m + 1))
    have hj : P.node P.length = Q.node 0 := hterm.trans hQinit.symm
    refine ⟨P.append Q hj, ?_, ?_, ?_, ?_⟩
    · simp only [append_length, hlen, hQlen, Finset.sum_range_succ]
    · simpa using hinit
    · simpa using (P.append_terminal Q hj).trans hQterm
    · apply P.append_property Q hj (fun A => A ⊆ U ∧ A.card ≤ B ∧ good A) hnode
      intro i
      exact ⟨(hQnode i).2.1.trans (Finset.union_subset (hnodes m (by omega)).1
          (hnodes (m + 1) (by omega)).1),
        (hQnode i).2.2.trans (max_le (hnodes m (by omega)).2 (hnodes (m + 1) (by omega)).2),
        hmono _ _ (hQnode i).1 (hinter m (by omega))⟩

/-- A fixed forced set adds no operations to a sampled path. -/
def withForced (P : SetOperationPath n) (D : Finset (Fin n)) : SetOperationPath n where
  length := P.length
  node i := D ∪ P.node i
  stationary i hi := congrArg (fun A => D ∪ A) (P.stationary i hi)
  step i := by
    have h := recourse_union_le D D (P.node (i + 1)) (P.node i)
    simp only [recourse, Finset.sdiff_self, Finset.union_self, Finset.card_empty, zero_add] at h
    exact h.trans (P.step i)

end SetOperationPath
end ConsistentSubmodular
