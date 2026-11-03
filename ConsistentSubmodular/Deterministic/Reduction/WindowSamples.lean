module

public import ConsistentSubmodular.Deterministic.Reduction.FractionalWindow
public import ConsistentSubmodular.Deterministic.Reduction.WindowCounts

@[expose] public section

/-! A finite rounded window certificate before single-operation realization. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

structure WindowSamples {n κ N T S : ℕ} {α : ℝ} {f : Objective n}
    {old initial terminal : Finset (Fin n)} {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
    (W : FractionalWindow f old Q hQ κ N T initial terminal α S) (H : ℕ) where
  forced : Finset (Fin n)
  forced_subset : forced ⊆ old
  forced_card : forced.card < H
  entryPieces : ℕ
  exitPieces : ℕ
  entry : Fin (entryPieces + 1) → Finset (Fin n)
  exit : Fin (exitPieces + 1) → Finset (Fin n)
  entry_initial : entry 0 = initial
  join : entry (Fin.last entryPieces) = exit 0
  exit_terminal : exit (Fin.last exitPieces) = terminal
  entry_subset : ∀ j, entry j ⊆ old
  exit_subset : ∀ j, exit j ⊆ old
  entry_card : ∀ j, ((entry j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N
  exit_card : ∀ j, ((exit j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N
  cost : (∑ j : Fin entryPieces, (recourse (entry j.castSucc) (entry j.succ) : ℝ)) +
    (∑ j : Fin exitPieces, (recourse (exit j.castSucc) (exit j.succ) : ℝ)) ≤
      8 * (S : ℝ) * (κ : ℝ)
  entry_first_good : (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
    f.value (Q 0 ∪ (forced ∪ entry 0))
  exit_first_good : (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
    f.value (Q T ∪ (forced ∪ exit 0))
  entry_intersection : ∀ j : Fin entryPieces,
    (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
      f.value (Q 0 ∪ (forced ∪ (entry j.castSucc ∩ entry j.succ)))
  exit_intersection : ∀ j : Fin exitPieces,
    (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
      f.value (Q T ∪ (forced ∪ (exit j.castSucc ∩ exit j.succ)))
  checkpoint_tests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ -
    f.bufferedOptimum old ∅ κ / N ≤
      f.value (Q (W.retained i) ∪ (forced ∪ entry (Fin.last entryPieces)))

end ConsistentSubmodular
