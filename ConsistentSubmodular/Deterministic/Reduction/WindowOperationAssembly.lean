module

public import ConsistentSubmodular.Deterministic.Reduction.RoundedWindow
public import ConsistentSubmodular.Deterministic.Reduction.WindowSamples

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace FractionalWindow

variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem rounded_of_zero_scale (hV : f.bufferedOptimum old ∅ κ = 0)
    (H L : ℕ) (hL : 2 ≤ L) : Nonempty (RoundedWindow W H L) := by
  classical
  obtain ⟨entry, helen, he0, he1, henodes⟩ :=
    SetOperationPath.exists_deletion_first initial (∅ : Finset (Fin n))
  obtain ⟨exit, hxlen, hx0, hx1, hxnodes⟩ :=
    SetOperationPath.exists_deletion_first (∅ : Finset (Fin n)) terminal
  have hinitcard : initial.card ≤ κ := by simpa only [W.core_initial] using W.core_card 0
  have htermcard : terminal.card ≤ κ := by
    simpa only [W.core_terminal] using W.core_card (Fin.last (3 * N + 1))
  have hinitold : initial ⊆ old := by simpa only [W.core_initial] using W.core_subset 0
  have htermold : terminal ⊆ old := by
    simpa only [W.core_terminal] using W.core_subset (Fin.last (3 * N + 1))
  have hcard (A : Finset (Fin n)) (hA : A.card ≤ κ) :
      (A.card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H := by
    have ha : (A.card : ℝ) ≤ κ := by exact_mod_cast hA
    have hd : 0 ≤ (κ : ℝ) / N := by positivity
    have hh : (0 : ℝ) ≤ H := by positivity
    linarith
  have hcoef : α - 2 / N ≤ 1 := by
    have hd : 0 ≤ (2 : ℝ) / N := by positivity
    linarith [W.level_le]
  have hgood (t : ℕ) (A : Finset (Fin n)) :
      (α - 2 / N) * f.bufferedOptimum old (Q t) κ ≤ f.value (Q t ∪ A) := by
    rw [f.bufferedOptimum_eq_of_zero_scale hV]
    exact (mul_le_of_le_one_left (f.nonnegative _) hcoef).trans
      (f.monotone _ _ Finset.subset_union_left)
  refine ⟨{
    entry := entry
    exit := exit
    entry_initial := he0
    join := he1.trans hx0.symm
    exit_terminal := hx1
    length := ?_
    entry_subset := ?_
    exit_subset := ?_
    entry_card := ?_
    exit_card := ?_
    entry_good := fun j => hgood 0 _
    exit_good := fun j => hgood T _
    checkpoint_tests := ?_ }⟩
  · rw [helen, hxlen]
    simp only [recourse, Finset.sdiff_empty, Finset.empty_sdiff,
      Finset.union_empty, Finset.empty_union]
    have hh := Nat.mul_le_mul_right κ hL
    omega
  · intro j
    have hh : entry.node j ⊆ initial := by simpa only [Finset.union_empty] using (henodes j).2.1
    exact hh.trans hinitold
  · intro j
    have hh : exit.node j ⊆ terminal := by simpa only [Finset.empty_union] using (hxnodes j).2.1
    exact hh.trans htermold
  · intro j
    apply hcard
    have hh := (henodes j).2.2
    simpa only [Finset.card_empty, Nat.zero_le, max_eq_left] using hh.trans
      (by simpa only [Finset.card_empty, Nat.zero_le, max_eq_left] using hinitcard)
  · intro j
    apply hcard
    have hh := (hxnodes j).2.2
    simpa only [Finset.card_empty, Nat.zero_le, max_eq_right] using hh.trans
      (by simpa only [Finset.card_empty, Nat.zero_le, max_eq_right] using htermcard)
  · intro i
    rw [hV, zero_div, sub_zero, he1, Finset.union_empty,
      f.bufferedOptimum_eq_of_zero_scale hV]
    exact mul_le_of_le_one_left (f.nonnegative _) (by linarith [W.level_le])

end FractionalWindow

namespace WindowSamples

variable {n κ N T S H : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  {W : FractionalWindow f old Q hQ κ N T initial terminal α S}
  (Smp : WindowSamples W H)

include Smp in
theorem toRounded (hκ : H ≤ κ) : Nonempty (RoundedWindow W H (windowLengthBound S)) := by
  classical
  let B := ⌊(κ : ℝ) + (κ : ℝ) / N⌋₊
  let Btotal := B + H
  let β : ℝ := α - 2 / N
  let goodE := fun A => β * f.bufferedOptimum old (Q 0) κ ≤ f.value (Q 0 ∪ A)
  let goodX := fun A => β * f.bufferedOptimum old (Q T) κ ≤ f.value (Q T ∪ A)
  have hmonoE : ∀ A B, A ⊆ B → goodE A → goodE B := by
    intro A B h hA
    exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right h))
  have hmonoX : ∀ A B, A ⊆ B → goodX A → goodX B := by
    intro A B h hA
    exact hA.trans (f.monotone _ _ (Finset.union_subset_union_right h))
  have hsubE : ∀ j, Smp.entry j ⊆ old ∧ (Smp.entry j).card ≤ B :=
    fun j => ⟨Smp.entry_subset j, Nat.le_floor (Smp.entry_card j)⟩
  have hsubX : ∀ j, Smp.exit j ⊆ old ∧ (Smp.exit j).card ≤ B :=
    fun j => ⟨Smp.exit_subset j, Nat.le_floor (Smp.exit_card j)⟩
  obtain ⟨E, hEl, hE0, hE1, hE⟩ := SetOperationPath.exists_chain_fin Smp.entry B old
    (fun A => goodE (Smp.forced ∪ A))
    (fun A B h => hmonoE _ _ (Finset.union_subset_union_right h))
    Smp.entry_first_good hsubE Smp.entry_intersection
  obtain ⟨X, hXl, hX0, hX1, hX⟩ := SetOperationPath.exists_chain_fin Smp.exit B old
    (fun A => goodX (Smp.forced ∪ A))
    (fun A B h => hmonoX _ _ (Finset.union_subset_union_right h))
    Smp.exit_first_good hsubX Smp.exit_intersection
  have hforced := Smp.forced_card.le
  have hκB : κ ≤ B := Nat.le_floor (by
    have : 0 ≤ (κ : ℝ) / N := by positivity
    linarith)
  have hinitcard : initial.card ≤ κ := by simpa only [W.core_initial] using W.core_card 0
  have htermcard : terminal.card ≤ κ := by
    simpa only [W.core_terminal] using W.core_card (Fin.last (3 * N + 1))
  have hinitold : initial ⊆ old := by simpa only [W.core_initial] using W.core_subset 0
  have htermold : terminal ⊆ old := by
    simpa only [W.core_terminal] using W.core_subset (Fin.last (3 * N + 1))
  have hβ : β ≤ 1 := by
    dsimp [β]
    have : 0 ≤ (2 : ℝ) / N := by positivity
    linarith [W.level_le]
  have hinitgood : goodE initial := by
    have hh := W.retained_optimal 0
    rw [W.retained_initial, W.core_initial] at hh
    dsimp [goodE]
    rw [hh]
    exact mul_le_of_le_one_left (f.bufferedOptimum_nonnegative _ _ _) hβ
  have htermgood : goodX terminal := by
    have hh := W.retained_optimal (Fin.last (3 * N + 1))
    rw [W.retained_terminal, W.core_terminal] at hh
    dsimp [goodX]
    rw [hh]
    exact mul_le_of_le_one_left (f.bufferedOptimum_nonnegative _ _ _) hβ
  have hEF (j : ℕ) : (E.withForced Smp.forced).node j ⊆ old ∧
      ((E.withForced Smp.forced).node j).card ≤ Btotal ∧ goodE ((E.withForced Smp.forced).node j) := by
    refine ⟨Finset.union_subset Smp.forced_subset (hE j).1, ?_, (hE j).2.2⟩
    exact (Finset.card_union_le _ _).trans (by dsimp [Btotal]; have := (hE j).2.1; omega)
  have hXF (j : ℕ) : (X.withForced Smp.forced).node j ⊆ old ∧
      ((X.withForced Smp.forced).node j).card ≤ Btotal ∧ goodX ((X.withForced Smp.forced).node j) := by
    refine ⟨Finset.union_subset Smp.forced_subset (hX j).1, ?_, (hX j).2.2⟩
    exact (Finset.card_union_le _ _).trans (by dsimp [Btotal]; have := (hX j).2.1; omega)
  obtain ⟨entry, hel, he0, he1, henode⟩ := (E.withForced Smp.forced).prepend_forced
    initial Smp.forced old Btotal goodE hmonoE
    (by change Smp.forced ∪ E.node 0 = _; rw [hE0, Smp.entry_initial]) hinitgood
    hinitold Smp.forced_subset (by dsimp [Btotal]; omega) hEF
  obtain ⟨exit, hxl, hx0, hx1, hxnode⟩ := (X.withForced Smp.forced).append_unforced
    terminal Smp.forced old Btotal goodX hmonoX
    (by change Smp.forced ∪ X.node X.length = _; rw [hX1, Smp.exit_terminal]) htermgood
    htermold Smp.forced_subset (by dsimp [Btotal]; omega) hXF
  have hcard (A : Finset (Fin n)) (hA : A.card ≤ Btotal) :
      (A.card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H := by
    have hb : (B : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N := Nat.floor_le (by positivity)
    have ha : (A.card : ℝ) ≤ (B : ℝ) + H := by exact_mod_cast hA
    linarith
  refine ⟨{
    entry := entry
    exit := exit
    entry_initial := he0
    join := ?_
    exit_terminal := hx1
    length := ?_
    entry_subset := fun j => (henode j).1
    exit_subset := fun j => (hxnode j).1
    entry_card := fun j => hcard _ (henode j).2.1
    exit_card := fun j => hcard _ (hxnode j).2.1
    entry_good := fun j => (henode j).2.2
    exit_good := fun j => (hxnode j).2.2
    checkpoint_tests := ?_ }⟩
  · rw [he1, hx0]
    change Smp.forced ∪ E.node E.length = Smp.forced ∪ X.node 0
    rw [hE1, hX0, Smp.join]
  · have hcost : E.length + X.length ≤ 8 * S * κ := by
      rw [hEl, hXl]
      exact_mod_cast Smp.cost
    have hcleanup : 2 * Smp.forced.card ≤ 2 * κ := by omega
    have hh := window_uniform_operation_count S κ (E.length + X.length)
      (2 * Smp.forced.card) hcost hcleanup
    rw [hel, hxl]
    change Smp.forced.card + E.length + (X.length + Smp.forced.card) ≤ _
    omega
  · intro i
    rw [he1]
    change _ ≤ f.value (Q (W.retained i) ∪ (Smp.forced ∪ E.node E.length))
    rw [hE1]
    exact Smp.checkpoint_tests i

end WindowSamples
end ConsistentSubmodular
