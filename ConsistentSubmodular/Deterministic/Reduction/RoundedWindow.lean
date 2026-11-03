module

public import ConsistentSubmodular.Deterministic.Reduction.WindowTransfer
public import ConsistentSubmodular.Deterministic.Reduction.ForcedPath
public import ConsistentSubmodular.Deterministic.Reduction.ResidualRounding
public import ConsistentSubmodular.Deterministic.Reduction.PathSubdivision
public import ConsistentSubmodular.Deterministic.Reduction.PhysicalIntersection
public import ConsistentSubmodular.Deterministic.Reduction.RoundingBudget
public import ConsistentSubmodular.Deterministic.Reduction.WindowCounts

@[expose] public section

/-! Finite physical realization of a baseline-compressed fractional window. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

structure RoundedWindow {n κ N T S : ℕ} {α : ℝ} {f : Objective n}
    {old initial terminal : Finset (Fin n)} {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
    (W : FractionalWindow f old Q hQ κ N T initial terminal α S) (H L : ℕ) where
  entry : SetOperationPath n
  exit : SetOperationPath n
  entry_initial : entry.node 0 = initial
  join : entry.node entry.length = exit.node 0
  exit_terminal : exit.node exit.length = terminal
  length : entry.length + exit.length ≤ L * κ
  entry_subset : ∀ j, entry.node j ⊆ old
  exit_subset : ∀ j, exit.node j ⊆ old
  entry_card : ∀ j, ((entry.node j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H
  exit_card : ∀ j, ((exit.node j).card : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N + H
  entry_good : ∀ j, (α - 2 / N) * f.bufferedOptimum old (Q 0) κ ≤
    f.value (Q 0 ∪ entry.node j)
  exit_good : ∀ j, (α - 2 / N) * f.bufferedOptimum old (Q T) κ ≤
    f.value (Q T ∪ exit.node j)
  checkpoint_tests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ -
    f.bufferedOptimum old ∅ κ / N ≤ f.value (Q (W.retained i) ∪ entry.node entry.length)

end ConsistentSubmodular
