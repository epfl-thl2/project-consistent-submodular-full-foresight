module

public import ConsistentSubmodular.Deterministic.Reduction.SamplingCardinality
public import ConsistentSubmodular.Deterministic.Reduction.ExponentialTails

@[expose] public section

/-! Simultaneous finite shared-threshold rounding (Appendix B.2.3). Each test is
controlled by an exponential tail bound as in Lemma B.7, and all tests by one
union bound. -/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

namespace ConsistentSubmodular

theorem Objective.insert_sub_le_singleton {n : ℕ} (f : Objective n) (A : Finset (Fin n))
    (e : Fin n) : f.value (insert e A) - f.value A ≤ f.value {e} - f.value ∅ := by
  have h := f.submodular A {e}
  have hm := f.monotone ∅ (A ∩ {e}) (Finset.empty_subset _)
  have hu : A ∪ {e} = insert e A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto
  rw [hu] at h
  linarith

/-- One deterministic threshold assignment simultaneously controls all tested
sizes, objective values of intersections, and the total number of changes.
The explicit probability budget is division-free and independent of the
ambient ground-set cardinality. -/
theorem exists_joint_rounding {n d : ℕ} {ι ε : Type*} [Fintype ι] [Fintype ε]
    (z : Fin d → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (g : ι → Objective n) (left right : ι → Fin d) (edgeLeft edgeRight : ε → Fin d)
    (κ L M a b R pSize pValue pCost : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (hcap : ∀ i e, (g i).value {e} - (g i).value ∅ ≤ L)
    (hmean : ∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
      (g i).value ≤ M)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * L * M)) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (d : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ S : Fin d → Finset (Fin n),
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ κ + b) ∧
      (∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
        (g i).value - a ≤ (g i).value (S (left i) ∩ S (right i))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by
  classical
  let T := fun e => Classical.choice (exists_sharedThreshold (fun t => z t e) (fun t => hz t e))
  let μ := FiniteLaw.product (fun e => (T e).law)
  let sample := fun ω t => sharedThresholdSample T ω t
  let size := fun t ω => ((sample ω t).card : ℝ)
  let value := fun i ω => (g i).value (sample ω (left i) ∩ sample ω (right i))
  let cost := fun ω => ∑ j, (recourse (sample ω (edgeLeft j)) (sample ω (edgeRight j)) : ℝ)
  have hvalueMean (i) : μ.expect (value i) =
      finiteExpectation (fun e => min (z (left i) e) (z (right i) e)) (g i).value :=
    sharedThresholdSample_intersection_expectation T (left i) (right i) (g i).value
  have hcostMean : μ.expect cost ≤ R * pCost := by
    dsimp only [cost]
    rw [μ.expect_sum]
    simpa only [μ, sample, sharedThresholdSample_recourse_expectation] using hcostBudget
  let bad : Fin d ⊕ (ι ⊕ Unit) → (∀ e, Fin (T e).cellCount) → Prop :=
    Sum.elim (fun t ω => κ + b < size t ω)
      (Sum.elim (fun i ω => value i ω < μ.expect (value i) - a)
        (fun _ ω => R ≤ cost ω))
  have hprobSize (t) : μ.probability (bad (.inl t)) ≤ pSize := by
    calc μ.probability (bad (.inl t))
        = finiteExpectation (z t) (fun S => if κ + b < (S.card : ℝ) then 1 else 0) := by
          rw [μ.probability_eq_expect, ← sharedThresholdSample_expectation T t]
          rfl
      _ = sampleExpectation Finset.univ (z t)
            (fun S => if κ + b < (S.card : ℝ) then 1 else 0) := (sampleExpectation_univ _ _).symm
      _ ≤ Real.exp (-(b ^ 2) / (4 * κ)) :=
          sampleExpectation_card_upper_tail Finset.univ (z t) (fun e _ => hz t e) (hsize t) hb hb2
      _ ≤ pSize := hsizeBudget
  have hprobValue (i) : μ.probability (bad (.inr (.inl i))) ≤ pValue := by
    let p := fun e => min (z (left i) e) (z (right i) e)
    have hp : ∀ e ∈ (Finset.univ : Finset (Fin n)), 0 ≤ p e ∧ p e ≤ 1 :=
      fun e _ => ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
    have hE : μ.expect (value i) = sampleExpectation Finset.univ p (g i).value := by
      rw [hvalueMean, sampleExpectation_univ]
    have hmean' : sampleExpectation Finset.univ p (g i).value - (g i).value ∅ ≤ M := by
      rw [sampleExpectation_univ]
      linarith [hmean i, (g i).nonnegative ∅]
    calc μ.probability (bad (.inr (.inl i)))
        = finiteExpectation p (fun S => if (g i).value S <
            sampleExpectation Finset.univ p (g i).value - a then 1 else 0) := by
          rw [μ.probability_eq_expect, ← sharedThresholdSample_intersection_expectation T]
          simp only [bad, value, hE, Sum.elim_inr, Sum.elim_inl]
          rfl
      _ = sampleExpectation Finset.univ p (fun S => if (g i).value S <
            sampleExpectation Finset.univ p (g i).value - a then 1 else 0) :=
          (sampleExpectation_univ _ _).symm
      _ ≤ Real.exp (-(a ^ 2) / (2 * L * M)) :=
          sampleExpectation_lower_tail Finset.univ p hp (g i).value (g i).monotone
            (g i).submodular hL (fun A e => ((g i).insert_sub_le_singleton A e).trans (hcap i e))
            hM hmean' ha
      _ ≤ pValue := hvalueBudget
  have hprobCost : μ.probability (bad (.inr (.inr ()))) ≤ pCost := by
    have h := (μ.markov (X := cost) (fun ω => Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)) R).trans hcostMean
    exact (mul_le_mul_iff_right₀ hR).mp h
  have hfailure : (∑ i, μ.probability (bad i)) < 1 := by
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hprobSize t)
    have hV := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hprobValue i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS hV
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    linarith
  obtain ⟨ω, hω, hgood⟩ := μ.exists_good_positive_of_sum_failure_lt_one bad hfailure
  refine ⟨sample ω, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t e he
    have hpos := FiniteLaw.coordinate_positive_of_product_positive (fun e => (T e).law) ω hω e
    have hnot := (T e).inactive_of_zero t he (ω e) hpos
    simpa [sample, sharedThresholdSample, FiniteLaw.selectedSet] using hnot
  · intro t e he
    have hpos := FiniteLaw.coordinate_positive_of_product_positive (fun e => (T e).law) ω hω e
    have hin := (T e).active_of_one t he (ω e) hpos
    simpa [sample, sharedThresholdSample, FiniteLaw.selectedSet] using hin
  · intro t
    exact le_of_not_gt (hgood (.inl t))
  · intro i
    have h := le_of_not_gt (hgood (.inr (.inl i)))
    change _ ≤ value i ω
    rw [← hvalueMean]
    exact h
  · exact lt_of_not_ge (hgood (.inr (.inr ())))
  · intro s t hst
    ext e
    simp only [sample, sharedThresholdSample, FiniteLaw.selectedSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(T e).ordered (ω e) s t (hst e).le,
      (T e).ordered (ω e) t s (hst e).symm.le⟩

end ConsistentSubmodular
