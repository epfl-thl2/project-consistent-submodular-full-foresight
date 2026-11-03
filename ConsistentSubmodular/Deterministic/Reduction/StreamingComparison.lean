module

public import ConsistentSubmodular.Deterministic.Reduction.StreamingParameters
public import ConsistentSubmodular.Deterministic.Reduction.Thinning
public import ConsistentSubmodular.Deterministic.Reduction.GlobalSchedule

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

namespace Objective

variable {n : ℕ} (f : Objective n)

theorem prefix_thinning_ratio {r k : ℕ} (hk : 0 < k) (hrk : r ≤ k)
    (δ : ℝ) (hδ : δ * k ≤ r) (t : ℕ) :
    δ * f.prefixOptimum k t ≤ f.prefixOptimum r t := by
  have hh := f.optimum_thinning (arrivedPrefix n t) hrk
  have hs := mul_le_mul_of_nonneg_right hδ (f.prefixOptimum_nonnegative k t)
  change (r : ℝ) * f.prefixOptimum k t ≤ (k : ℝ) * f.prefixOptimum r t at hh
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  apply (mul_le_mul_iff_right₀ hk0).mp
  nlinarith only [hh, hs]

theorem transfer_comparison {N H k : ℕ} (p : TransferParameters N H k) {α : ℝ}
    (hα : α ≤ 1) (hγ : 0 ≤ α - 14 * ((1 : ℝ) / N)) (hk : 0 < k) (s t : ℕ)
    (hstable : f.prefixOptimum k t ≤ (1 + (1 : ℝ) / N) * f.prefixOptimum k s) :
    (α - 14 * ((1 : ℝ) / N)) * f.prefixOptimum k t ≤
      (α - 2 * ((1 : ℝ) / N)) * f.prefixOptimum p.core s := by
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hβ : 0 ≤ α - 2 * ((1 : ℝ) / N) := by linarith
  have hthin := f.prefix_thinning_ratio hk p.core_le _ p.thinning s
  have hslack := stable_slack_comparison α ((1 : ℝ) / N) hα hη0
  have h1 := mul_le_mul_of_nonneg_left hstable hγ
  have h2 := mul_le_mul_of_nonneg_right hslack (f.prefixOptimum_nonnegative k s)
  have h3 := mul_le_mul_of_nonneg_left hthin hβ
  nlinarith only [h1, h2, h3]

end Objective

namespace ProtectedPrograms

variable {n N H k R : ℕ} {f : Objective n} {α : ℝ}
variable (p : TransferParameters N H k)
variable {C : ProtectedClock (f.prefixOptimum k) ((1 : ℝ) / N) p.block p.interval}
variable (P : ProtectedPrograms f p.core (α - 2 * ((1 : ℝ) / N)) C R
  (p.core + p.block + H))

/-- A family of rounded local programs yields a valid finite trajectory with
one uniform per-update rate and the required fractional approximation. -/
theorem trajectory_spec (hk : 0 < k) (hα : α ≤ 3 / 4)
    (hγ : 0 ≤ α - 14 * ((1 : ℝ) / N)) :
    FeasibleTrajectory k (R + 2) (fun t : Fin (n + 1) => P.selected t.val) ∧
      ∀ (t : Fin (n + 1)) (A : Finset (Fin n)),
        A ⊆ arrivedPrefix n t.val → A.card ≤ k →
        (α - 14 * ((1 : ℝ) / N)) * f.value A ≤ f.value (P.selected t.val) := by
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  refine ⟨?_, ?_⟩
  · refine ⟨P.selected_zero, ?_, ?_⟩
    · intro t
      exact ⟨P.arrived_bound _, (P.cardinality_bound _).trans (by have := p.capacity; omega)⟩
    · intro t
      exact P.recourse_bound p.block_pos t.val
  · intro t A hA hAk
    have hopt : f.value A ≤ f.prefixOptimum k t.val := by
      simpa [Objective.prefixOptimum] using f.le_bufferedOptimum (Q := ∅) hA hAk
    have hv := P.value_bound p.block_pos hη0 (by linarith)
      (fun s t hs => f.transfer_comparison p (by linarith) hγ hk s t hs) t.val
    exact (mul_le_mul_of_nonneg_left hopt hγ).trans hv

end ProtectedPrograms
end ConsistentSubmodular
