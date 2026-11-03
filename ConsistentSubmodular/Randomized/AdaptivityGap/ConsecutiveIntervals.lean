module

public import ConsistentSubmodular.Randomized.AdaptivityGap.ConsecutiveChains
public import ConsistentSubmodular.Randomized.AdaptivityGap.EqualizingDistribution

@[expose] public section

/-!
# Lemma 4: consecutive intervals with the equalizing distribution

The proof of Lemma 4 in Appendix A.6. For nonincreasing consecutive intervals with
lengths `d_0 ≥ ... ≥ d_N > 0` (Definition 2.3), the equalizing distribution has the
cumulative probabilities (5), so every fixed interval has expected value `B + d_N`,
where `B = E[ℓ_j]`; interval `j` is a best interval in hindsight at realization
`j`, so the expected value in hindsight is `B + C` with `C = E[d_j]`. Summation by
parts gives `B = Σ_j (d_j - d_N)` and `C = d_N (1 + Σ_j (1 - d_{j+1}/d_j))`, so the
bound `Γ ≥ ξ⋆` is the chain inequality (14) for the chain `d_j / d_N`; the paper
scales the endpoints so that `d_N = 1`. Inequality (14) is proved in
`ConsecutiveChains`. The three intervals `[0, 1]`, `[1, 1 + u₁]`,
`[1 + u₁, 1 + u₁ + u₂]` of the extremal chain (17) attain `Γ = ξ⋆`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Chains

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

/-- Interval `j` is a best interval in hindsight for realization `j`: earlier
intervals have no surviving length, and later intervals have length at most `d_j`. -/
theorem maxValue_eq (j : Fin (N + 1)) :
    Finset.univ.sup' Finset.univ_nonempty (fun i => I.value i j) =
      I.left j + intervalLength I j := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    rw [value_eq hI]
    split_ifs with h
    · linarith [length_antitone hI h]
    · linarith [length_pos hI j]
  · apply Finset.le_sup'_of_le _ (Finset.mem_univ j)
    rw [value_eq hI, if_pos le_rfl]

/-- `C = E[d_j] ≥ d_N`. -/
theorem length_last_le_expectedLength :
    intervalLength I (Fin.last N) ≤ ∑ j, I.prob j * intervalLength I j := by
  calc intervalLength I (Fin.last N) = ∑ j, I.prob j * intervalLength I (Fin.last N) := by
        rw [← Finset.sum_mul, I.prob_sum, one_mul]
    _ ≤ ∑ j, I.prob j * intervalLength I j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (length_antitone hI (Fin.le_last j)) (I.prob_nonneg j)

/-- `ℓ_j = Σ_{i < j} d_i`, since the intervals are consecutive from `ℓ_0 = 0`. -/
theorem left_eq_sum (j : Fin (N + 1)) :
    I.left j = ∑ i, if i < j then intervalLength I i else 0 := by
  induction j using Fin.induction with
  | zero =>
    rw [hI.1]
    symm
    exact Finset.sum_eq_zero fun i _ => if_neg (Fin.not_lt_zero i)
  | succ j ih =>
    rw [hI.2.1 j, show I.right j.castSucc = I.left j.castSucc + intervalLength I j.castSucc by
      unfold intervalLength; ring, ih]
    have h : ∀ i : Fin (N + 1), (if i < j.succ then intervalLength I i else 0) =
        (if i < j.castSucc then intervalLength I i else 0) +
          (if i = j.castSucc then intervalLength I i else 0) := by
      intro i
      have hlt : i < j.succ ↔ i < j.castSucc ∨ i = j.castSucc := by
        rw [Fin.lt_def, Fin.lt_def, Fin.ext_iff]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      by_cases h1 : i < j.castSucc
      · have h2 : i ≠ j.castSucc := ne_of_lt h1
        rw [if_pos (hlt.mpr (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
      · by_cases h2 : i = j.castSucc
        · rw [if_pos (hlt.mpr (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (fun h => (hlt.mp h).elim h1 h2), if_neg h1, if_neg h2, add_zero]
    rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp

end Consecutive

section Equalizing

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
  (hE : I.IsEqualizing)
include hI hE

/-- The cumulative probabilities (5) of the equalizing distribution. -/
theorem cumulative_prob (i : Fin (N + 1)) :
    ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i :=
  (isEqualizing_iff hI).mp hE i

/-- Every fixed interval has expected value `E[ℓ_j] + d_N`. -/
theorem expectedValue_eq (i : Fin (N + 1)) :
    ∑ j, I.prob j * I.value i j = ∑ j, I.prob j * I.left j + intervalLength I (Fin.last N) := by
  rw [expectedValue_eq_cumulative hI, cumulative_prob hI hE i, mul_div_assoc',
    mul_div_cancel_left₀ _ (length_pos hI i).ne']

/-- `Γ = (B + d_N) / (B + C)` with `B = E[ℓ_j]` and `C = E[d_j]`. -/
theorem adaptivityGap_eq : I.adaptivityGap =
    (∑ j, I.prob j * I.left j + intervalLength I (Fin.last N)) /
      (∑ j, I.prob j * I.left j + ∑ j, I.prob j * intervalLength I j) := by
  have hfix : I.fixedValue = ∑ j, I.prob j * I.left j + intervalLength I (Fin.last N) := by
    unfold IntervalInstance.fixedValue
    simp_rw [expectedValue_eq hI hE]
    exact Finset.sup'_const _ _
  have hada : I.adaptiveValue = ∑ j, I.prob j * I.left j + ∑ j, I.prob j * intervalLength I j := by
    unfold IntervalInstance.adaptiveValue
    simp_rw [maxValue_eq hI, mul_add, Finset.sum_add_distrib]
  have hB : 0 ≤ ∑ j, I.prob j * I.left j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (I.prob_nonneg j) (I.left_nonneg j)
  have hC := length_last_le_expectedLength hI
  have hpos : 0 < I.adaptiveValue := by
    rw [hada]
    linarith [length_pos hI (Fin.last N)]
  unfold IntervalInstance.adaptivityGap
  rw [if_neg hpos.ne', hfix, hada]

/-! ### Summation by parts -/

theorem prob_zero : I.prob 0 = intervalLength I (Fin.last N) / intervalLength I 0 := by
  have h : ∑ i ∈ Finset.Iic 0, I.prob i = intervalLength I (Fin.last N) / intervalLength I 0 :=
    cumulative_prob hI hE 0
  rw [sum_Iic_eq] at h
  rw [← h, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [if_neg]
    rw [Fin.le_iff_val_le_val]
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp only [Fin.val_zero]
    omega
  · simp

theorem prob_succ (j : Fin N) :
    I.prob j.succ = intervalLength I (Fin.last N) / intervalLength I j.succ -
      intervalLength I (Fin.last N) / intervalLength I j.castSucc := by
  have h1 : ∑ i ∈ Finset.Iic j.succ, I.prob i =
      intervalLength I (Fin.last N) / intervalLength I j.succ := cumulative_prob hI hE j.succ
  have h2 : ∑ i ∈ Finset.Iic j.castSucc, I.prob i =
      intervalLength I (Fin.last N) / intervalLength I j.castSucc := cumulative_prob hI hE j.castSucc
  rw [sum_Iic_eq] at h1 h2
  rw [← h1, ← h2, ← Finset.sum_sub_distrib, Finset.sum_eq_single j.succ]
  · rw [if_pos le_rfl, if_neg (not_le.mpr Fin.castSucc_lt_succ), sub_zero]
  · intro b _ hb
    split_ifs with hb1 hb2 hb2
    · ring
    · exfalso
      rw [Fin.le_iff_val_le_val] at hb1 hb2
      simp only [Fin.val_succ, Fin.val_castSucc] at hb1 hb2
      exact hb (Fin.ext (by simp only [Fin.val_succ]; omega))
    · exfalso
      rw [Fin.le_iff_val_le_val] at hb1 hb2
      simp only [Fin.val_succ, Fin.val_castSucc] at hb1 hb2
      omega
    · ring
  · simp

/-- `C = E[d_j] = d_N (1 + Σ_j (1 - d_{j+1}/d_j))`. -/
theorem expectedLength_eq : ∑ j, I.prob j * intervalLength I j =
    intervalLength I (Fin.last N) + intervalLength I (Fin.last N) *
      ∑ j : Fin N, (1 - intervalLength I j.succ / intervalLength I j.castSucc) := by
  rw [Fin.sum_univ_succ, prob_zero hI hE, div_mul_cancel₀ _ (length_pos hI 0).ne', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [prob_succ hI hE]
  have h1 := (length_pos hI j.succ).ne'
  have h2 := (length_pos hI j.castSucc).ne'
  field_simp

/-- `B = E[ℓ_j] = Σ_j (d_j - d_N)`. -/
theorem expectedLeft_eq : ∑ j, I.prob j * I.left j =
    ∑ j : Fin N, (intervalLength I j.castSucc - intervalLength I (Fin.last N)) := by
  have htail : ∀ i : Fin (N + 1), ∑ j, (if i < j then I.prob j else 0) =
      1 - intervalLength I (Fin.last N) / intervalLength I i := by
    intro i
    have h : ∑ j ∈ Finset.Iic i, I.prob j =
        intervalLength I (Fin.last N) / intervalLength I i := cumulative_prob hI hE i
    rw [← h, sum_Iic_eq, ← I.prob_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ≤ i
    · rw [if_neg (not_lt.mpr h), if_pos h, sub_self]
    · rw [if_pos (lt_of_not_ge h), if_neg h, sub_zero]
  calc ∑ j, I.prob j * I.left j
      = ∑ j, ∑ i, (if i < j then I.prob j * intervalLength I i else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [left_eq_sum hI j, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> ring
    _ = ∑ i, intervalLength I i * ∑ j, (if i < j then I.prob j else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
    _ = ∑ i, (intervalLength I i - intervalLength I (Fin.last N)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [htail i]
        have := (length_pos hI i).ne'
        field_simp
    _ = ∑ j : Fin N, (intervalLength I j.castSucc - intervalLength I (Fin.last N)) := by
        rw [Fin.sum_univ_castSucc, sub_self, add_zero]

/-- **Lemma 4**, the bound: `Γ ≥ ξ⋆` for nonincreasing consecutive intervals with the
equalizing distribution. For the chain `d_j / d_N`, the claim `ξ⋆ (B + C) ≤ B + d_N` is
`C - d_N ≤ q (B + d_N)`, which is the chain inequality (14) multiplied by `d_N`. -/
theorem xiStar_le_adaptivityGap : xiStar ≤ I.adaptivityGap := by
  set dN := intervalLength I (Fin.last N) with hdN
  have hdN0 : 0 < dN := length_pos hI (Fin.last N)
  have hchain := sum_edgeValue_le (fun j => intervalLength I j / dN)
    (fun i j hij => div_le_div_of_nonneg_right (length_antitone hI hij) hdN0.le)
    (div_self hdN0.ne')
  -- `d_N Σ_j φ(d_j / d_N, d_{j+1} / d_N) = (C - d_N) - q B`.
  have hscaled : dN * ∑ j : Fin N, edgeValue (intervalLength I j.castSucc / dN)
      (intervalLength I j.succ / dN) =
      dN * ∑ j : Fin N, (1 - intervalLength I j.succ / intervalLength I j.castSucc) -
        qStar * ∑ j : Fin N, (intervalLength I j.castSucc - dN) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := (length_pos hI j.castSucc).ne'
    unfold edgeValue
    field_simp
  have hB := expectedLeft_eq hI hE
  have hC := expectedLength_eq hI hE
  rw [← hdN] at hB hC
  have hineq : ∑ j, I.prob j * intervalLength I j - dN ≤
      qStar * (∑ j, I.prob j * I.left j + dN) := by
    have := mul_le_mul_of_nonneg_left hchain hdN0.le
    rw [hscaled] at this
    rw [hC, hB]
    nlinarith
  have hBnn : 0 ≤ ∑ j, I.prob j * I.left j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (I.prob_nonneg j) (I.left_nonneg j)
  have hCdN := length_last_le_expectedLength hI
  rw [← hdN] at hCdN
  rw [adaptivityGap_eq hI hE, ← hdN, le_div_iff₀ (by linarith), xiStar_eq_qStar]
  have hq := qStar_pos
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by linarith)]
  linarith

end Equalizing

/-! ### The equality case -/

theorem uTwo_div_uOne : uOne ^ 2 * (1 + uOne) / uOne = uOne * (1 + uOne) := by
  have := uOne_pos
  field_simp

/-- The three intervals `[0, 1]`, `[1, 1 + u₁]`, `[1 + u₁, 1 + u₁ + u₂]` with the
probabilities `(u₂, u₂/u₁ - u₂, 1 - u₂/u₁)`: the extremal chain (17)
`d_0 = 1/u₂`, `d_1 = u₁/u₂`, `d_2 = 1`, with all endpoints scaled by `u₂`. -/
def extremalInstance : IntervalInstance 2 where
  left := ![0, 1, 1 + uOne]
  right := ![1, 1 + uOne, 1 + uOne + uOne ^ 2 * (1 + uOne)]
  prob := ![uOne ^ 2 * (1 + uOne), uOne ^ 2 * (1 + uOne) / uOne - uOne ^ 2 * (1 + uOne),
    1 - uOne ^ 2 * (1 + uOne) / uOne]
  left_nonneg i := by
    have := uOne_pos
    fin_cases i
    · simp
    · simp
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      linarith
  left_le_right i := by
    have := uOne_pos
    fin_cases i
    · simp
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val]
      nlinarith
  prob_nonneg i := by
    have h0 := uOne_pos
    have hb := uOne_bounds
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      positivity
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, uTwo_div_uOne]
      nlinarith
    · simp only [Fin.reduceFinMk, Matrix.cons_val, uTwo_div_uOne]
      nlinarith
  prob_sum := by
    simp [Fin.sum_univ_succ]

theorem extremalInstance_consecutive : extremalInstance.IsNonincreasingConsecutive := by
  have h0 := uOne_pos
  have hb := uOne_bounds
  have hu2 : 0 < uOne ^ 2 * (1 + uOne) := by positivity
  refine ⟨by simp [extremalInstance], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp [extremalInstance]
    · simp [extremalInstance]
  · intro i
    fin_cases i
    · simp [extremalInstance]
      linarith
    · simp [extremalInstance]
      nlinarith
  · simp [extremalInstance]
    exact hu2

/-- The probabilities `(u₂, u₂/u₁ - u₂, 1 - u₂/u₁)` have the cumulative sums (5), so
they are the equalizing distribution of the three intervals. -/
theorem extremalInstance_equalizing : extremalInstance.IsEqualizing := by
  have h0 := uOne_pos
  rw [isEqualizing_iff extremalInstance_consecutive]
  intro j
  rw [sum_Iic_eq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, intervalLength]
  fin_cases j
  · simp [extremalInstance]
  · simp [extremalInstance, uTwo_div_uOne]
  · simp [extremalInstance, uTwo_div_uOne]
    field_simp

theorem extremalInstance_gap : extremalInstance.adaptivityGap = xiStar := by
  have h0 := uOne_pos
  have hphi := phi_uOne
  unfold phi at hphi
  have hB : ∑ j, extremalInstance.prob j * extremalInstance.left j =
      (uOne * (1 + uOne) - uOne ^ 2 * (1 + uOne)) + (1 - uOne * (1 + uOne)) * (1 + uOne) := by
    simp [Fin.sum_univ_succ, extremalInstance, uTwo_div_uOne]
  have hC : ∑ j, extremalInstance.prob j * intervalLength extremalInstance j =
      uOne ^ 2 * (1 + uOne) + (uOne * (1 + uOne) - uOne ^ 2 * (1 + uOne)) * uOne +
        (1 - uOne * (1 + uOne)) * (uOne ^ 2 * (1 + uOne)) := by
    simp [Fin.sum_univ_succ, extremalInstance, intervalLength, uTwo_div_uOne]
    ring
  have hdN : intervalLength extremalInstance (Fin.last 2) = uOne ^ 2 * (1 + uOne) := by
    simp [intervalLength, extremalInstance]
  rw [adaptivityGap_eq extremalInstance_consecutive extremalInstance_equalizing, xiStar_eq_uOne, hB, hC, hdN,
    div_eq_div_iff (by nlinarith [uOne_bounds]) (by positivity)]
  linear_combination (-(uOne ^ 2 * (1 + uOne))) * hphi

/-- **Lemma 4**: every instance of nonincreasing consecutive intervals with the
equalizing distribution has `Γ ≥ ξ⋆`, with equality for the three intervals
`[0, 1]`, `[1, 1 + u₁]`, `[1 + u₁, 1 + u₁ + u₂]`. -/
theorem consecutiveIntervalGap : ConsecutiveIntervalGapGoal :=
  ⟨fun _ _ hI hE => xiStar_le_adaptivityGap hI hE, uOne, uOne ^ 2 * (1 + uOne), uOne_pos,
    uOne_lt_one, phi_uOne, fun _ hx0 hx1 hx => eq_uOne hx0.le hx1.le hx, rfl, extremalInstance,
    extremalInstance_consecutive, extremalInstance_equalizing, extremalInstance_gap, rfl, rfl,
    rfl⟩

end ConsistentSubmodular.Chains
