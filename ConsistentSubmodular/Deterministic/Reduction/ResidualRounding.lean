module

public import ConsistentSubmodular.Deterministic.Reduction.FiniteJointRounding
public import ConsistentSubmodular.Deterministic.Reduction.SamplingScale

@[expose] public section

/-! Shared rounding after forcing high marginal elements. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem exists_residual_rounding {τ ι ε : Type*} [Fintype τ] [Fintype ι] [Fintype ε]
    (U : Finset (Fin n)) (κ H : ℕ) (hH : 0 < H) (hHκ : H ≤ κ)
    (V : ℝ) (hV : 0 < V) (hscale : ∀ A ⊆ U, A.card ≤ κ → f.value A ≤ V)
    (z : τ → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (hsupport : ∀ t e, e ∉ U → z t e = 0) (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (Q : ι → Finset (Fin n)) (left right : ι → τ) (edgeLeft edgeRight : ε → τ)
    (target : ι → ℝ)
    (htarget : ∀ i, target i ≤ finiteExpectation
      (fun e => min (z (left i) e) (z (right i) e)) (fun S => f.value (Q i ∪ S)))
    (a b R pSize pValue pCost : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * (V / H) * (2 * V))) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (Fintype.card τ : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ D : Finset (Fin n), ∃ S : τ → Finset (Fin n), D ⊆ U ∧ D.card < H ∧
      (∀ t, S t ⊆ U) ∧
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ (κ : ℝ) + b) ∧
      (∀ i, target i - a ≤ f.value (Q i ∪ (D ∪ (S (left i) ∩ S (right i))))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by
  classical
  have hHr : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  have hκ : 0 < κ := lt_of_lt_of_le hH hHκ
  have hpay : V ≤ (H : ℝ) * (V / H) := by rw [mul_div_cancel₀ _ (ne_of_gt hHr)]
  obtain ⟨D, hDU, hDH, hcap⟩ := f.exists_forced_set U κ H hH hHκ (V / H) V hscale hpay
  have hmincube (i : ι) (e) :
      0 ≤ min (z (left i) e) (z (right i) e) ∧ min (z (left i) e) (z (right i) e) ≤ 1 :=
    ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
  have hminmass (i : ι) : (∑ e, min (z (left i) e) (z (right i) e)) ≤ κ :=
    (Finset.sum_le_sum (fun e _ => min_le_left _ _)).trans (hsize (left i))
  have hminsupport (i : ι) (e) (he : e ∉ U) : min (z (left i) e) (z (right i) e) = 0 := by
    simp [hsupport _ e he]
  obtain ⟨S, hzero, hone, hcard, hval, hcost, hequal⟩ := exists_finite_joint_rounding z hz
    (fun i => f.contractOn U (D ∪ Q i)) left right edgeLeft edgeRight
    κ (V / H) (2 * V) a b R pSize pValue pCost ha hb hb2 hR (div_pos hV hHr) (by positivity)
    hsize (fun i => f.contractOn_singleton_cap U D (Q i) (div_nonneg hV.le hHr.le) hcap)
    (fun i => f.contractOn_expectation_le U (D ∪ Q i) κ hκ hV.le hscale _ (hmincube i) (hminmass i))
    hsizeBudget hvalueBudget hcostBudget hbudget
  have hSU (t) : S t ⊆ U := by
    intro e he
    by_contra heU
    exact hzero t e (hsupport t e heU) he
  refine ⟨D, S, hDU, hDH, hSU, hzero, hone, hcard, ?_, hcost, hequal⟩
  intro i
  have hlift := f.contractOn_expectation_add_forced_lower U D (Q i) _
    (hmincube i) (hminsupport i)
  have h := hval i
  have hint : (S (left i) ∩ S (right i)) ∩ U = S (left i) ∩ S (right i) :=
    Finset.inter_eq_left.mpr (Finset.inter_subset_left.trans (hSU (left i)))
  change _ ≤ f.value ((D ∪ Q i) ∪ ((S (left i) ∩ S (right i)) ∩ U)) - f.value (D ∪ Q i) at h
  rw [hint] at h
  have hunion : (D ∪ Q i) ∪ (S (left i) ∩ S (right i)) =
      Q i ∪ (D ∪ (S (left i) ∩ S (right i))) := by ext e; simp; tauto
  rw [hunion] at h
  linarith [htarget i]

end ConsistentSubmodular.Objective
