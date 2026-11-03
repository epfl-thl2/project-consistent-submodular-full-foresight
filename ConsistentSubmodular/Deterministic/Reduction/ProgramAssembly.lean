module

public import ConsistentSubmodular.Deterministic.Reduction.GlobalSchedule
public import ConsistentSubmodular.Deterministic.Reduction.PhysicalOperationPath

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

structure RoundedWindowFamily {n b ell : ℕ} (f : Objective n) (κ : ℕ) (β : ℝ)
    {F : ℕ → ℝ} {η : ℝ} (C : ProtectedClock F η b ell) (B L : ℕ) where
  entry : ℕ → SetOperationPath n
  exit : ℕ → SetOperationPath n
  join : ∀ i, (entry i).node (entry i).length = (exit i).node 0
  initial_card : ∀ i, ((entry i).node 0).card ≤ κ
  entry_card : ∀ i j, ((entry i).node j).card ≤ B
  exit_card : ∀ i j, ((exit i).node j).card ≤ B
  entry_arrived : ∀ i j, (entry i).node j ⊆ arrivedPrefix n (C.start i)
  exit_arrived : ∀ i j, (exit i).node j ⊆ arrivedPrefix n (C.start i)
  length : ∀ i, (entry i).length + (exit i).length ≤ L * κ
  entry_value : ∀ i j, β * f.prefixOptimum κ (C.start i) ≤ f.value ((entry i).node j)
  exit_value : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((exit i).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))
  checkpoint_value : ∀ i t, C.start i ≤ t → t ≤ C.start (i + 1) →
    β * f.prefixOptimum κ t ≤ f.value ((entry i).node (entry i).length ∪
      (arrivedPrefix n t \ arrivedPrefix n (C.start i)))

structure RoundedBridgeFamily {n b ell κ B L : ℕ} {f : Objective n} {β η : ℝ}
    {F : ℕ → ℝ} {C : ProtectedClock F η b ell}
    (W : RoundedWindowFamily f κ β C B L) where
  path : ℕ → SetOperationPath n
  initial : ∀ i, (path i).node 0 = (W.exit i).node (W.exit i).length
  terminal : ∀ i, (path i).node (path i).length = (W.entry (i + 1)).node 0
  cardinality : ∀ i j, ((path i).node j).card ≤ B
  arrived : ∀ i j, (path i).node j ⊆ arrivedPrefix n (C.start (i + 1))
  length : ∀ i, (path i).length ≤ L * κ
  value : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((path i).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))

namespace RoundedWindowFamily

variable {n b ell κ B L R : ℕ} {f : Objective n} {β η : ℝ}
variable {F : ℕ → ℝ} {C : ProtectedClock F η b ell}
variable (W : RoundedWindowFamily f κ β C B L) (T : RoundedBridgeFamily W)

include W T in
theorem assemble (hκB : κ ≤ B) (hrate : (3 * L + 1) * κ ≤ R * ell) :
    Nonempty (ProtectedPrograms f κ β C R B) := by
  classical
  obtain ⟨init, hinitlen, hinit0, hinit1, hinitgood⟩ :=
    SetOperationPath.exists_deletion_first (∅ : Finset (Fin n)) ((W.entry 0).node 0)
  have hinitjoin : init.node init.length = (W.entry 0).node 0 := hinit1
  let first := init.append (W.entry 0) hinitjoin
  let old := fun i => (W.exit i).append (T.path i) (T.initial i).symm
  have hj (i : ℕ) : (old i).node (old i).length = (W.entry (i + 1)).node 0 := by
    dsimp [old]
    simp only [SetOperationPath.append_terminal, T.terminal]
  let next := fun i => (old i).append (W.entry (i + 1)) (hj i)
  let P : ℕ → SetOperationPath n := fun i => match i with | 0 => first | i + 1 => next i
  have hterminal (i : ℕ) : (P i).node (P i).length = (W.entry i).node (W.entry i).length := by
    cases i <;> simp [P, first, next, SetOperationPath.append_terminal]
  have hPinitial (i : ℕ) : (P (i + 1)).node 0 = (W.exit i).node 0 := by
    simp [P, next, old]
  have hinitcard (j : ℕ) : (init.node j).card ≤ B := by
    have hh := (hinitgood j).2.2
    have hi := W.initial_card 0
    simp only [Finset.card_empty, zero_le, max_eq_right] at hh
    omega
  have hinitarrived (j : ℕ) : init.node j ⊆ arrivedPrefix n (C.start 0) := by
    have hh := (hinitgood j).2.1
    simp only [Finset.empty_union] at hh
    exact hh.trans (W.entry_arrived 0 0)
  refine ⟨{
    path := P
    initial := by simp [P, first, hinit0]
    joins := fun i => by rw [hterminal, hPinitial, W.join]
    length := ?_
    cardinality := ?_
    arrived := ?_
    transition := ?_
    checkpoint := ?_ }⟩
  · intro i
    cases i with
    | zero =>
      have hi : init.length ≤ κ := by
        rw [hinitlen]
        simpa [recourse] using W.initial_card 0
      have he := W.length 0
      change first.length ≤ R * ell
      simp only [first, SetOperationPath.append_length]
      nlinarith
    | succ i =>
      have he0 := W.length i
      have he1 := W.length (i + 1)
      have hb := T.length i
      change (next i).length ≤ R * ell
      simp only [next, old, SetOperationPath.append_length]
      nlinarith
  · intro i
    cases i with
    | zero =>
      exact init.append_property (W.entry 0) hinitjoin (fun A => A.card ≤ B)
        hinitcard (W.entry_card 0)
    | succ i =>
      exact (old i).append_property (W.entry (i + 1)) (hj i) (fun A => A.card ≤ B)
        ((W.exit i).append_property (T.path i) (T.initial i).symm (fun A => A.card ≤ B)
          (W.exit_card i) (T.cardinality i))
        (W.entry_card (i + 1))
  · intro i
    cases i with
    | zero =>
      exact init.append_property (W.entry 0) hinitjoin
        (fun A => A ⊆ arrivedPrefix n (C.start 0)) hinitarrived (W.entry_arrived 0)
    | succ i =>
      exact (old i).append_property (W.entry (i + 1)) (hj i)
        (fun A => A ⊆ arrivedPrefix n (C.start (i + 1)))
        ((W.exit i).append_property (T.path i) (T.initial i).symm
          (fun A => A ⊆ arrivedPrefix n (C.start (i + 1)))
          (fun j => (W.exit_arrived i j).trans (arrivedPrefix_mono
            (C.start_mono (show i ≤ i + 1 by omega)))) (T.arrived i))
        (W.entry_arrived (i + 1))
  · intro i
    let good := fun A => β * f.prefixOptimum κ (C.start (i + 1)) ≤
      f.value (A ∪ (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))
    exact (old i).append_property (W.entry (i + 1)) (hj i) good
      ((W.exit i).append_property (T.path i) (T.initial i).symm good (W.exit_value i) (T.value i))
      (fun j => (W.entry_value (i + 1) j).trans
        (f.monotone _ _ Finset.subset_union_left))
  · intro i t ht0 ht1
    rw [hterminal]
    exact W.checkpoint_value i t ht0 ht1

end RoundedWindowFamily
end ConsistentSubmodular
