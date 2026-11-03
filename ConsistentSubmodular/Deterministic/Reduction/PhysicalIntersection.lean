module

public import ConsistentSubmodular.Deterministic.Reduction.TypeLipschitz
public import ConsistentSubmodular.Deterministic.Basic.PhysicalSampling
public import ConsistentSubmodular.Deterministic.Basic.Simplex

@[expose] public section

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

/-- The shared-threshold physical intersection loses at most `V` times the
type distance. Physical core overlap is handled before the scalar loss bound. -/
theorem physical_intersection_lower {n m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n))
    (V : ℝ) (hV : 0 ≤ V) (hcore : ∀ i, f.value (cores i) ≤ V)
    (p q : Point m) (hp : IsSimplex p) (hq : IsSimplex q) :
    finiteExpectation p (f.onTypes cores B).value - V * (∑ i, |p i - q i|) ≤
      finiteExpectation (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
        (fun A => f.value (B ∪ A)) := by
  have hsing : ∀ i, (f.onTypes cores B).value {i}-(f.onTypes cores B).value ∅ ≤ V := by
    intro i
    rw [Objective.onTypes_singleton, Objective.onTypes_empty]
    have hh := f.subadditive B (cores i)
    linarith [hcore i]
  have hpc : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩
  have hqc : ∀ i, 0 ≤ q i ∧ q i ≤ 1 := fun i => ⟨hq.1 i, hq.coordinate_le_one i⟩
  have htype := (f.onTypes cores B).finiteExpectation_min_lower V hV hsing p q hpc hqc
  have hmin0 : ∀ i, 0 ≤ min (p i) (q i) := fun i => le_min (hp.1 i) (hq.1 i)
  have hmass : (∑ i, min (p i) (q i)) ≤ 1 :=
    (Finset.sum_le_sum (fun i _ => min_le_left _ _)).trans_eq hp.2
  have hlift := physical_multilinear_lift f cores B (fun i => min (p i) (q i)) hmin0 hmass
  have hsmall : ∀ e, 0 ≤ physicalProbability cores (fun i => min (p i) (q i)) e ∧
      physicalProbability cores (fun i => min (p i) (q i)) e ≤ 1 := by
    intro e
    exact ⟨physicalProbability_nonnegative cores _ hmin0 e,
      (physicalProbability_le_mass cores _ hmin0 e).trans hmass⟩
  have hlarge : ∀ e, 0 ≤ min (physicalProbability cores p e) (physicalProbability cores q e) ∧
      min (physicalProbability cores p e) (physicalProbability cores q e) ≤ 1 := by
    intro e
    exact ⟨le_min (physicalProbability_mem_unitInterval cores p hp e).1
      (physicalProbability_mem_unitInterval cores q hq e).1,
      (min_le_left _ _).trans (physicalProbability_mem_unitInterval cores p hp e).2⟩
  have hm := f.sampleAdd_mono_probability Finset.univ
    (physicalProbability cores (fun i => min (p i) (q i)))
    (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
    (fun e _ => hsmall e) (fun e _ => hlarge e)
    (fun e _ => physicalProbability_min_le cores p q e) B
  have hm' : finiteExpectation (physicalProbability cores (fun i => min (p i) (q i)))
      (fun A => f.value (B ∪ A)) ≤
      finiteExpectation (fun e => min (physicalProbability cores p e) (physicalProbability cores q e))
        (fun A => f.value (B ∪ A)) := by
    simpa only [sampleAdd, sampleExpectation_univ] using hm
  exact htype.trans (hlift.trans hm')

end ConsistentSubmodular
