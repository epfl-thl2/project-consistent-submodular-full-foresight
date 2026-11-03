module

public import ConsistentSubmodular.Deterministic.Reduction.SamplingCardinality
public import ConsistentSubmodular.Deterministic.Reduction.ForcedSet
public import ConsistentSubmodular.Deterministic.Basic.PhysicalSampling

@[expose] public section

/-! Contracted residual objectives and their uniform sampling scale. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

/-- Restrict to the old ground set and subtract the fixed buffer baseline. -/
def contractOn (U B : Finset (Fin n)) : Objective n where
  value S := f.value (B ∪ (S ∩ U)) - f.value B
  nonnegative S := sub_nonneg.mpr (f.monotone _ _ Finset.subset_union_left)
  monotone S T h := sub_le_sub_right (f.monotone _ _
    (Finset.union_subset_union_right (Finset.inter_subset_inter h (Finset.Subset.refl U)))) _
  submodular S T := by
    have h := f.submodular (B ∪ (S ∩ U)) (B ∪ (T ∩ U))
    have hu : (B ∪ (S ∩ U)) ∪ (B ∪ (T ∩ U)) = B ∪ ((S ∪ T) ∩ U) := by
      ext e; simp; tauto
    have hi : (B ∪ (S ∩ U)) ∩ (B ∪ (T ∩ U)) = B ∪ ((S ∩ T) ∩ U) := by
      ext e; simp; tauto
    rw [hu, hi] at h
    linarith

@[simp] theorem contractOn_empty (U B : Finset (Fin n)) : (f.contractOn U B).value ∅ = 0 := by
  simp [contractOn]

theorem contractOn_le (U B S : Finset (Fin n)) :
    (f.contractOn U B).value S ≤ f.value (S ∩ U) := by
  have h := f.subadditive B (S ∩ U)
  change f.value (B ∪ (S ∩ U)) - f.value B ≤ f.value (S ∩ U)
  linarith

theorem contractOn_expectation_eq (U B : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (f.contractOn U B).value =
      finiteExpectation p (fun S => f.value (B ∪ S)) - f.value B := by
  rw [← sampleExpectation_univ, ← sampleExpectation_univ]
  rw [sampleExpectation_inter_zero U Finset.univ p hp,
    sampleExpectation_inter_zero U Finset.univ p hp, Finset.univ_inter]
  have he : sampleExpectation U p (f.contractOn U B).value =
      sampleExpectation U p (fun S => f.value (B ∪ S) - f.value B) := by
    apply sampleExpectation_congr
    intro S hS
    simp [contractOn, Finset.inter_eq_left.mpr hS]
  rw [he, sampleExpectation_sub, sampleExpectation_const]

theorem contractOn_expectation_add_forced_lower (U D Q : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1) (hsupport : ∀ e ∉ U, p e = 0) :
    finiteExpectation p (fun S => f.value (Q ∪ S)) - f.value (D ∪ Q) ≤
      finiteExpectation p (f.contractOn U (D ∪ Q)).value := by
  rw [f.contractOn_expectation_eq U (D ∪ Q) p hsupport]
  apply sub_le_sub_right
  exact finiteExpectation_mono p hp (fun S => f.monotone _ _
    (Finset.union_subset_union_left Finset.subset_union_right))

theorem contractOn_singleton_cap (U D Q : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) :
    ∀ e, (f.contractOn U (D ∪ Q)).value {e} - (f.contractOn U (D ∪ Q)).value ∅ ≤ c := by
  intro e
  rw [contractOn_empty, sub_zero]
  by_cases heU : e ∈ U
  · have hint : {e} ∩ U = {e} := Finset.inter_eq_left.mpr (by simpa using heU)
    change f.value ((D ∪ Q) ∪ ({e} ∩ U)) - f.value (D ∪ Q) ≤ c
    rw [hint, Finset.union_singleton]
    by_cases heD : e ∈ D
    · simp [Finset.mem_union_left Q heD, hc]
    · exact f.forced_marginal_under_buffer D Q e (hcap e heU heD)
  · have hint : {e} ∩ U = ∅ := by simp [heU]
    simpa [contractOn, hint] using hc

/-- A cardinality-constrained optimum bounds every larger set after thinning.
This loose affine bound is convenient under an arbitrary product law. -/
theorem cardinality_scale_bound (U : Finset (Fin n)) (k : ℕ) {V : ℝ}
    (hV : 0 ≤ V) (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (S : Finset (Fin n)) (hSU : S ⊆ U) :
    (k : ℝ) * f.value S ≤ ((k : ℝ) + S.card) * V := by
  by_cases hk : S.card ≤ k
  · have h := mul_le_mul_of_nonneg_left (hscale S hSU hk) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have hcard := mul_nonneg (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card) hV
    nlinarith
  · obtain ⟨A, hAS, hAk, hthin⟩ := f.exists_thinned_subset S k (by omega)
    have hA := hscale A (hAS.trans hSU) (by omega)
    have h := hthin.trans (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg S.card))
    have hkV := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hV
    nlinarith

/-- Contracting any buffer, even a large one, leaves expected residual at most
twice the old cardinality-constrained optimum. -/
theorem contractOn_expectation_le (U B : Finset (Fin n)) (k : ℕ) (hk : 0 < k)
    {V : ℝ} (hV : 0 ≤ V)
    (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (p : Fin n → ℝ) (hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1)
    (hmass : ∑ e, p e ≤ k) :
    finiteExpectation p (f.contractOn U B).value ≤ 2 * V := by
  have hpoint (S : Finset (Fin n)) :
      (k : ℝ) * (f.contractOn U B).value S ≤ (k : ℝ) * V + V * S.card := by
    have hcontract := mul_le_mul_of_nonneg_left (f.contractOn_le U B S) (Nat.cast_nonneg k)
    have hscaleS := f.cardinality_scale_bound U k hV hscale (S ∩ U) Finset.inter_subset_right
    have hcard : ((S ∩ U).card : ℝ) ≤ S.card := Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_left)
    have hprod := mul_le_mul_of_nonneg_right hcard hV
    nlinarith
  have he := finiteExpectation_mono p hp hpoint
  rw [finiteExpectation_mul, finiteExpectation_add, finiteExpectation_const,
    finiteExpectation_mul, finiteExpectation_card] at he
  have hm := mul_le_mul_of_nonneg_left hmass hV
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  nlinarith

end ConsistentSubmodular.Objective
