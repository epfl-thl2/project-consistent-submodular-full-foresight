module

public import ConsistentSubmodular.Deterministic.Basic.FiniteMaxCoverage
public import ConsistentSubmodular.Deterministic.Reduction.FiniteProductLaw

@[expose] public section

/-!
Finite shared thresholds realized by the nested finite maximum decomposition.
Each physical coordinate has one law shared by every tested probability.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

namespace MaximumCoverage

variable {d : ℕ} {w : Fin d → ℝ} (R : MaximumCoverage w)

theorem singleton_weight (hw : ∀ i, 0 ≤ w i) (i : Fin d) :
    (∑ a, if i ∈ R.labels a then R.weight a else 0) = w i := by
  have h := R.value_eq {i}
  rw [finiteMaximum_singleton i w (hw i)] at h
  have hmem (a) : (R.labels a ∩ {i}).Nonempty ↔ i ∈ R.labels a := by
    constructor
    · rintro ⟨x, hx⟩
      have hxi := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      simpa [hxi] using (Finset.mem_inter.mp hx).1
    · intro hi
      exact ⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_singleton_self i⟩⟩
  simpa only [hmem] using h.symm

theorem total_weight : (∑ a, R.weight a) = finiteMaximum Finset.univ w := by
  simpa [R.labels_nonempty] using (R.value_eq Finset.univ).symm

end MaximumCoverage

structure SharedThreshold {d : ℕ} (z : Fin d → ℝ) where
  cellCount : ℕ
  law : FiniteLaw (Fin cellCount)
  active : Fin cellCount → Finset (Fin d)
  inclusion : ∀ t, law.probability (fun ω => t ∈ active ω) = z t
  ordered : ∀ ω s t, z s ≤ z t → s ∈ active ω → t ∈ active ω

theorem exists_sharedThreshold {d : ℕ} (z : Fin d → ℝ) (hz : ∀ t, 0 ≤ z t ∧ z t ≤ 1) :
    Nonempty (SharedThreshold z) := by
  classical
  obtain ⟨R⟩ := exists_maximumCoverage z (fun t => (hz t).1)
  let M := finiteMaximum Finset.univ z
  have hM : M ≤ 1 := finiteMaximum_le (by norm_num) (fun t _ => (hz t).2)
  refine ⟨{
    cellCount := R.atomCount + 1
    law := {
      weight := Fin.cases (1 - M) R.weight
      nonnegative := ?_
      sum_one := ?_
    }
    active := Fin.cases ∅ R.labels
    inclusion := ?_
    ordered := ?_
  }⟩
  · intro ω
    exact Fin.cases (sub_nonneg.mpr hM) (fun a => (R.weight_positive a).le) ω
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [R.total_weight]
    dsimp [M]
    ring
  · intro t
    unfold FiniteLaw.probability
    dsimp only
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, Finset.notMem_empty, ite_false, zero_add]
    exact R.singleton_weight (fun t => (hz t).1) t
  · intro ω
    refine Fin.cases ?_ ?_ ω
    · intro s t _ hs
      exact (Finset.notMem_empty s hs).elim
    · intro a s t hst hs
      exact R.labels_upward a s t hst hs

namespace SharedThreshold

variable {d : ℕ} {z : Fin d → ℝ} (T : SharedThreshold z)

theorem inactive_of_zero (t : Fin d) (hz : z t = 0) (ω : Fin T.cellCount)
    (hω : 0 < T.law.weight ω) : t ∉ T.active ω := by
  intro ht
  have h := T.law.weight_le_probability (fun a => t ∈ T.active a) ω ht
  rw [T.inclusion, hz] at h
  linarith

theorem active_of_one (t : Fin d) (hz : z t = 1) (ω : Fin T.cellCount)
    (hω : 0 < T.law.weight ω) : t ∈ T.active ω := by
  by_contra ht
  have h := T.law.weight_le_probability (fun a => t ∉ T.active a) ω ht
  rw [T.law.probability_not, T.inclusion, hz] at h
  linarith

theorem intersection_probability (s t : Fin d) :
    T.law.probability (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = min (z s) (z t) := by
  rcases le_total (z s) (z t) with hst | hts
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => s ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.left, fun hs => ⟨hs, T.ordered ω s t hst hs⟩⟩
    rw [heq, T.inclusion, min_eq_left hst]
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => t ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.right, fun ht => ⟨T.ordered ω t s hts ht, ht⟩⟩
    rw [heq, T.inclusion, min_eq_right hts]

theorem change_probability (s t : Fin d) :
    T.law.probability (fun ω =>
      (s ∈ T.active ω ∧ t ∉ T.active ω) ∨ (t ∈ T.active ω ∧ s ∉ T.active ω)) = |z s - z t| := by
  classical
  have hid : T.law.probability (fun ω =>
      (s ∈ T.active ω ∧ t ∉ T.active ω) ∨ (t ∈ T.active ω ∧ s ∉ T.active ω)) =
      T.law.probability (fun ω => s ∈ T.active ω) + T.law.probability (fun ω => t ∈ T.active ω) -
        2 * T.law.probability (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) := by
    unfold FiniteLaw.probability
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ω _
    dsimp only
    by_cases hs : s ∈ T.active ω <;> by_cases ht : t ∈ T.active ω <;> simp [hs, ht]
    ring
  rw [hid, T.inclusion, T.inclusion, T.intersection_probability]
  rcases le_total (z s) (z t) with hst | hts
  · rw [min_eq_left hst, abs_of_nonpos (sub_nonpos.mpr hst)]
    ring
  · rw [min_eq_right hts, abs_of_nonneg (sub_nonneg.mpr hts)]
    ring

end SharedThreshold

variable {n d : ℕ}

def sharedThresholdSample {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e))
    (ω : ∀ e, Fin (T e).cellCount) (t : Fin d) : Finset (Fin n) :=
  FiniteLaw.selectedSet (fun e a => t ∈ (T e).active a) ω

theorem sharedThresholdSample_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (t : Fin d)
    (v : Finset (Fin n) → ℝ) :
    (FiniteLaw.product (fun e => (T e).law)).expect (fun ω => v (sharedThresholdSample T ω t)) =
      finiteExpectation (z t) v := by
  unfold sharedThresholdSample
  rw [FiniteLaw.product_selected_expectation]
  have hp : (fun e => (T e).law.probability (fun a => t ∈ (T e).active a)) = z t :=
    funext (fun e => (T e).inclusion t)
  rw [hp]

theorem sharedThresholdSample_intersection_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (s t : Fin d)
    (v : Finset (Fin n) → ℝ) :
    (FiniteLaw.product (fun e => (T e).law)).expect
      (fun ω => v (sharedThresholdSample T ω s ∩ sharedThresholdSample T ω t)) =
      finiteExpectation (fun e => min (z s e) (z t e)) v := by
  have hsample (ω : ∀ e, Fin (T e).cellCount) :
      sharedThresholdSample T ω s ∩ sharedThresholdSample T ω t =
        FiniteLaw.selectedSet (fun e a => s ∈ (T e).active a ∧ t ∈ (T e).active a) ω := by
    ext e
    simp [sharedThresholdSample, FiniteLaw.selectedSet]
  simp_rw [hsample]
  rw [FiniteLaw.product_selected_expectation]
  have hp : (fun e => (T e).law.probability (fun a => s ∈ (T e).active a ∧ t ∈ (T e).active a)) =
      (fun e => min (z s e) (z t e)) := funext (fun e => (T e).intersection_probability s t)
  rw [hp]

end ConsistentSubmodular
