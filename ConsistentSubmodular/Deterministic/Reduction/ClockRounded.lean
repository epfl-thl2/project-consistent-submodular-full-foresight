module

public import ConsistentSubmodular.Deterministic.Reduction.ClockWindows
public import ConsistentSubmodular.Deterministic.Reduction.RoundedWindow
public import ConsistentSubmodular.Deterministic.Reduction.ProgramAssembly

@[expose] public section

/-! Local rounded objects retain their pure optimizer endpoints when indexed by
a protected clock. This module assembles them into families. -/

noncomputable section
namespace ConsistentSubmodular
namespace ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)
variable {n : ℕ} (f : Objective n) (κ : ℕ) (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N)
variable (HW LW HB LB B L : ℕ)

/-- Assemble independently rounded windows and their pure-endpoint bridges.
All comparisons use the actual prefix optimum at the corresponding clock time. -/
theorem rounded_families
    (R : ∀ i, RoundedWindow (C.fractionalWindows f κ O N (by omega) i) HW LW)
    (hcardW : (κ : ℝ) + κ / N + HW ≤ B) (hcardB : (κ : ℝ) + κ / N + HB ≤ B)
    (hLW : LW ≤ L) (hLB : LB ≤ L)
    (bridges : ∀ i, ∃ P : SetOperationPath n,
      P.node 0 = C.windowTerminal f κ i ∧ P.node P.length = C.windowInitial f κ (i + 1) ∧
      P.length ≤ LB * κ ∧ ∀ j, P.node j ⊆ C.windowTerminal f κ i ∪ C.windowInitial f κ (i + 1) ∧
        ((P.node j).card : ℝ) ≤ κ + κ / N + HB ∧
        (O.level - 2 / N) * f.prefixOptimum κ (C.start (i + 1)) ≤
          f.value (C.windowBuffer n i (C.windowDuration i) ∪ P.node j)) :
    ∃ W : RoundedWindowFamily f κ (O.level - 2 * ((1 : ℝ) / N)) C B L,
      Nonempty (RoundedBridgeFamily W) := by
  have hN0 : 0 < N := by omega
  let W : RoundedWindowFamily f κ (O.level - 2 * ((1 : ℝ) / N)) C B L := {
    entry := fun i => (R i).entry
    exit := fun i => (R i).exit
    join := fun i => (R i).join
    initial_card := fun i => by rw [(R i).entry_initial]; exact (C.windowInitial_spec f κ i).2.1
    entry_card := fun i j => by exact_mod_cast ((R i).entry_card j).trans hcardW
    exit_card := fun i j => by exact_mod_cast ((R i).exit_card j).trans hcardW
    entry_arrived := fun i j => (R i).entry_subset j
    exit_arrived := fun i j => (R i).exit_subset j
    length := fun i => (R i).length.trans (Nat.mul_le_mul_right κ hLW)
    entry_value := fun i j => by
      have hh := (R i).entry_good j
      simpa only [C.windowBuffer_zero, Finset.empty_union, Objective.prefixOptimum,
        windowOld, mul_one_div] using hh
    exit_value := fun i j => by
      have hh := (R i).exit_good j
      have hb := C.window_benchmark_dominates f κ i (C.windowDuration i)
      rw [C.windowDuration_end] at hb
      have hg : (O.level - 2 / N) * f.prefixOptimum κ (C.start (i + 1)) ≤
          f.value (C.windowBuffer n i (C.windowDuration i) ∪ (R i).exit.node j) := by
        by_cases hβ : 0 ≤ O.level - 2 / N
        · exact (mul_le_mul_of_nonneg_left hb hβ).trans hh
        · have hp := f.prefixOptimum_nonnegative κ (C.start (i + 1))
          have hf := f.nonnegative (C.windowBuffer n i (C.windowDuration i) ∪ (R i).exit.node j)
          nlinarith
      simpa only [C.windowBuffer_terminal, Finset.union_comm, mul_one_div] using hg
    checkpoint_value := fun i t ht0 ht1 => by
      have hh := C.retained_tests_prefix f κ O N hN0 i ((R i).entry.node (R i).entry.length)
        ((R i).checkpoint_tests) t ht0 ht1
      simpa only [mul_one_div] using hh }
  let P := fun i => Classical.choose (bridges i)
  have hP i := Classical.choose_spec (bridges i)
  refine ⟨W, ⟨{
    path := P
    initial := ?_
    terminal := ?_
    cardinality := ?_
    arrived := ?_
    length := ?_
    value := ?_ }⟩⟩
  · intro i
    exact (hP i).1.trans (R i).exit_terminal.symm
  · intro i
    exact (hP i).2.1.trans (R (i + 1)).entry_initial.symm
  · intro i j
    exact_mod_cast ((hP i).2.2.2 j).2.1.trans hcardB
  · intro i j
    exact ((hP i).2.2.2 j).1.trans (C.window_bridge_arrived f κ i)
  · intro i
    exact (hP i).2.2.1.trans (Nat.mul_le_mul_right κ hLB)
  · intro i j
    have hh := ((hP i).2.2.2 j).2.2
    simpa only [P, C.windowBuffer_terminal, Finset.union_comm, mul_one_div] using hh

end ProtectedClock
end ConsistentSubmodular
