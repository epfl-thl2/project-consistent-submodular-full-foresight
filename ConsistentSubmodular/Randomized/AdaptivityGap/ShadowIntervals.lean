module

public import ConsistentSubmodular.Randomized.AdaptivityGap.StepIntegrals

@[expose] public section

/-!
# Shadow intervals

The first step of the proof of Lemma 3 (Appendix A.5). For a realization `j`, let
`d_j = max_i |I_i ∩ [ℓ_j, ∞)|` and `Î_j = [ℓ_j, ℓ_j + d_j]`; its right endpoint `ℓ_j + d_j` is the
value in hindsight at realization `j`. An interval `I_{i(j)}` attaining `d_j`, cut at `ℓ_j`, is a
rightward translate of `Î_j`, so it dominates `Î_j` against every left endpoint (6). The shadow
intervals therefore have the same expected value in hindsight and a smaller best fixed value, and
inequality (7) for the shadow intervals proves `α E[max_i v(i, j)] ≤ max_i E[v(i, j)]`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Shadow

/-- Inequality (6) for one interval `[a, b]` and one left endpoint `c`: with
`d = |[a, b] ∩ [c, ∞)|`, the shadow interval `[c, c + d]` satisfies
`|[c, c + d] ∩ [x, ∞)| ≤ |[a, b] ∩ [x, ∞)|` for every `x`. -/
theorem shadow_le (a b c x : ℝ) :
    max 0 (c + max 0 (b - max a c) - max c x) ≤ max 0 (b - max a x) := by
  simp only [max_def]
  split_ifs <;> linarith

variable {N : ℕ} (I : IntervalInstance N)

/-- The value in hindsight `max_i v(i, j) = ℓ_j + d_j`, the right endpoint of the shadow
interval `Î_j`. -/
def hindsight (j : Fin (N + 1)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => I.value i j

theorem left_le_hindsight (j : Fin (N + 1)) : I.left j ≤ hindsight I j :=
  (le_add_of_nonneg_right (le_max_left _ _)).trans
    (Finset.le_sup' (fun i => I.value i j) (Finset.mem_univ j))

/-- Inequality (6): some original interval dominates the shadow interval `Î_j` against every
left endpoint. -/
theorem exists_dominating (j : Fin (N + 1)) : ∃ i, ∀ x,
    max 0 (hindsight I j - max (I.left j) x) ≤ max 0 (I.right i - max (I.left i) x) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty fun i => I.value i j
  refine ⟨i, fun x => ?_⟩
  rw [hindsight, hi, IntervalInstance.value]
  exact shadow_le _ _ _ _

theorem support_nonempty : (Finset.univ.filter fun j => I.prob j ≠ 0).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := I.prob)
    (by rw [I.prob_sum]; exact one_ne_zero)
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

/-- The law of the random left endpoint `ℓ_J`, `J ∼ p`. Its smallest point is the smallest left
endpoint of positive probability, so zero-probability realizations play no role. -/
def leftLaw : LeftLaw (Fin (N + 1)) where
  prob := I.prob
  left := I.left
  low := (Finset.univ.filter fun j => I.prob j ≠ 0).inf' (support_nonempty I) I.left
  prob_nonneg := I.prob_nonneg
  prob_sum := I.prob_sum
  low_le j hj := Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)
  atom := by
    obtain ⟨j, hj, hjl⟩ := Finset.exists_mem_eq_inf' (support_nonempty I) I.left
    exact ⟨j, (Finset.mem_filter.mp hj).2, hjl.ge⟩

/-- **The shadow reduction.** Under the hypothesis of Lemma 3,
`α E[max_i v(i, j)] ≤ max_i E[v(i, j)]`: inequality (7) for the shadow intervals, with
`M = max_i E_j |I_i ∩ [ℓ_j, ∞)|` bounding their own values by (6). -/
theorem shadow_bound {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α) :
    α * I.adaptiveValue ≤ I.fixedValue := by
  have hlow : 0 ≤ (leftLaw I).low :=
    Finset.le_inf' (support_nonempty I) I.left fun j _ => I.left_nonneg j
  have hcore := (leftLaw I).core_le hα0 hα1 hchain hlow (hindsight I)
    (fun j _ => left_le_hindsight I j) (M := I.fixedValue - (leftLaw I).mean) fun i _ => by
      obtain ⟨i', hi'⟩ := exists_dominating I i
      calc ∑ j, I.prob j * max 0 (hindsight I i - max (I.left i) (I.left j))
          ≤ ∑ j, I.prob j * max 0 (I.right i' - max (I.left i') (I.left j)) :=
            Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi' _) (I.prob_nonneg j)
        _ = ∑ j, I.prob j * I.value i' j - (leftLaw I).mean := by
            simp only [IntervalInstance.value, mul_add, Finset.sum_add_distrib, LeftLaw.mean,
              leftLaw]
            ring
        _ ≤ I.fixedValue - (leftLaw I).mean :=
            sub_le_sub_right (Finset.le_sup' (fun i => ∑ j, I.prob j * I.value i j)
              (Finset.mem_univ i')) _
  have hada : I.adaptiveValue =
      (leftLaw I).mean + ∑ j, (leftLaw I).prob j * (hindsight I j - (leftLaw I).left j) := by
    simp only [IntervalInstance.adaptiveValue, LeftLaw.mean, leftLaw, hindsight, mul_sub,
      Finset.sum_sub_distrib]
    ring
  rw [hada]
  linarith

end ConsistentSubmodular.Shadow
