module

public import ConsistentSubmodular.Deterministic.Reduction.FractionalWindow

@[expose] public section

/-! Finite retained tests extend to every physical time, and the anchor's
guarantee at a retained stage lifts to independent sampling even when physical
cores overlap. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace FractionalWindow
variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem retained_tests_extend (hN : 0 < N) (A : Finset (Fin n)) (loss : ℝ) (hloss : 0 ≤ loss)
    (htests : ∀ i, α * f.bufferedOptimum old (Q (W.retained i)) κ - loss ≤
      f.value (Q (W.retained i) ∪ A)) :
    ∀ t, t ≤ T → α * f.bufferedOptimum old (Q t) κ - loss-
      α * (f.bufferedOptimum old ∅ κ / N) ≤ f.value (Q t ∪ A) := by
  have hNr : (0 : ℝ) ≤ N := by positivity
  have hwidth : 0 ≤ f.bufferedOptimum old ∅ κ / N :=
    div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr
  have hα0 := W.level_nonneg
  have hα := W.level_le
  intro t ht
  rcases W.retained_covers t ht with hhigh | ⟨i, hit, hbin⟩
  · have hu := f.bufferedOptimum_le old (Q t) κ
    have hm := f.monotone (Q t) (Q t ∪ A) Finset.subset_union_left
    have h0 := f.nonnegative ∅
    have hv : f.bufferedOptimum old (Q t) κ ≤ f.value (Q t) + f.bufferedOptimum old ∅ κ := by
      linarith only [hu, h0]
    have h1 := mul_le_mul_of_nonneg_left hv hα0
    have h2 := mul_le_mul_of_nonneg_right hα (show 0 ≤ f.value (Q t) + f.bufferedOptimum old ∅ κ by
      linarith only [f.nonnegative (Q t), f.bufferedOptimum_nonnegative old ∅ κ])
    nlinarith only [h1, h2, hm, hhigh, hloss, mul_nonneg hα0 hwidth]
  · have hg := f.bufferedOptimum_growth (N := old) (k := κ) (hQ hit)
    have hm := f.monotone (Q (W.retained i) ∪ A) (Q t ∪ A) (Finset.union_subset_union_left (hQ hit))
    have hs := (htests i).trans hm
    have hd : f.bufferedOptimum old (Q t) κ ≤
        f.bufferedOptimum old (Q (W.retained i)) κ + f.bufferedOptimum old ∅ κ / N := by
      linarith only [hg, hbin]
    have h1 := mul_le_mul_of_nonneg_left hd hα0
    linarith only [h1, hs]

theorem retained_physical (i : Fin (3 * N + 2)) :
    α * f.bufferedOptimum old (Q (W.retained i)) κ ≤
      finiteExpectation (physicalProbability W.cores W.checkpoint)
        (fun A => f.value (Q (W.retained i) ∪ A)) :=
  (W.checkpoint_retained i).trans (physical_multilinear_lift f W.cores (Q (W.retained i))
    W.checkpoint W.simplex.1 W.simplex.2.le)

end FractionalWindow
end ConsistentSubmodular
