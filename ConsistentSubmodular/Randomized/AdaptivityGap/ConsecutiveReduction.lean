module

public import ConsistentSubmodular.Randomized.AdaptivityGap.ShadowIntervals

@[expose] public section

/-!
# Lemma 3: reduction to consecutive intervals

Lemma 3 of the paper (Appendix A.5): if every instance of nonincreasing consecutive intervals with
the equalizing distribution has adaptivity gap at least `α ∈ [0, 1]`, then so does every
interval-selection instance. The proof follows the paper:

* `ShadowIntervals`: the shadow intervals and inequality (6) reduce the claim to inequality (7);
* `StepIntegrals`: inequality (7), through the distribution function `W`, its integral `H`, the
  inverse `X = H⁻¹`, `g = 1 / (W ∘ X)`, the extension (9), identities (10) and (11), and the
  average of the chains `g(s), g(s + 1), …` over `s ∈ [0, 1]`;
* `EqualizingDistribution` and `ShadowChains`: the hypothesis applied to one chain with its
  equalizing distribution (5), using the computation from the proof of Lemma 4.

The proof never divides by `α`, so the case `α = 0` needs no separate argument.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Shadow

theorem adaptiveValue_nonneg {N : ℕ} (I : IntervalInstance N) : 0 ≤ I.adaptiveValue :=
  Finset.sum_nonneg fun j _ =>
    mul_nonneg (I.prob_nonneg j) ((I.left_nonneg j).trans (left_le_hindsight I j))

/-- **Lemma 3** (reduction to consecutive intervals). -/
theorem consecutiveIntervalReduction : ConsecutiveIntervalReductionGoal := by
  intro α hα0 hα1 hchain N I
  rw [IntervalInstance.adaptivityGap]
  split_ifs with h0
  · exact hα1
  · rw [le_div_iff₀ (lt_of_le_of_ne (adaptiveValue_nonneg I) (Ne.symm h0))]
    exact shadow_bound I hα0 hα1 hchain

end ConsistentSubmodular.Shadow
