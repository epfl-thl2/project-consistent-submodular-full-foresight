module

public import ConsistentSubmodular.Deterministic.Reduction.SharedThreshold

@[expose] public section

/-! Exact cardinality and change expectations for shared finite thresholds. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

theorem finiteExpectation_card {n : ℕ} (p : Fin n → ℝ) :
    finiteExpectation p (fun S => (S.card : ℝ)) = ∑ e, p e := by
  have hcard : (fun S : Finset (Fin n) => (S.card : ℝ)) =
      (fun S => ∑ e : Fin n, if e ∈ S then (1 : ℝ) else 0) := by
    funext S
    simp
  rw [hcard, finiteExpectation_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hmem (S : Finset (Fin n)) : ({e} ∩ S).Nonempty ↔ e ∈ S := by
    constructor
    · rintro ⟨x, hx⟩
      have hxe := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).1
      simpa [hxe] using (Finset.mem_inter.mp hx).2
    · intro he
      exact ⟨e, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self e, he⟩⟩
  simpa only [hmem, Finset.prod_singleton, sub_sub_cancel] using finiteExpectation_hit p {e}

variable {n d : ℕ}

theorem sharedThresholdSample_recourse_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (s t : Fin d) :
    (FiniteLaw.product (fun e => (T e).law)).expect
      (fun ω => (recourse (sharedThresholdSample T ω s) (sharedThresholdSample T ω t) : ℝ)) =
      ∑ e, |z s e - z t e| := by
  let changed := fun (e : Fin n) (a : Fin (T e).cellCount) =>
    (s ∈ (T e).active a ∧ t ∉ (T e).active a) ∨ (t ∈ (T e).active a ∧ s ∉ (T e).active a)
  have hchange (ω : ∀ e, Fin (T e).cellCount) :
      recourse (sharedThresholdSample T ω s) (sharedThresholdSample T ω t) =
        (FiniteLaw.selectedSet changed ω).card := by
    unfold recourse
    congr 1
    ext e
    simp only [sharedThresholdSample, FiniteLaw.selectedSet, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_univ, true_and, changed]
  simp_rw [hchange]
  rw [FiniteLaw.product_selected_expectation (fun e => (T e).law) changed
    (fun S => (S.card : ℝ)), finiteExpectation_card]
  apply Finset.sum_congr rfl
  intro e _
  exact (T e).change_probability s t

end ConsistentSubmodular
