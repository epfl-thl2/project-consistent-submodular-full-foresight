module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# The equalizing distribution

The derivation that opens Appendix A.5. For nonincreasing consecutive intervals
(Definition 2.3), interval `i` gains its length `d_i = r_i - ℓ_i` at the
realizations `j ≤ i` and nothing at later ones, so every fixed interval has
expected value `E_{j∼p}[v(i, j)] = E_{j∼p}[ℓ_j] + d_i Σ_{j ≤ i} p_j`. Since
`Σ_j p_j = 1`, these values are equal for all `i` exactly when the cumulative
probabilities are (5): `Σ_{j ≤ i} p_j = d_N / d_i` for every `i`. Every fixed
interval then has expected value `E_{j∼p}[ℓ_j] + d_N`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- The length `d_j = r_j - ℓ_j` of interval `j`. -/
def intervalLength {N : ℕ} (I : IntervalInstance N) (j : Fin (N + 1)) : ℝ :=
  I.right j - I.left j

theorem sum_Iic_eq {N : ℕ} (f : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i, if i ≤ j then f i else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp

section Consecutive

variable {N : ℕ} {I : IntervalInstance N} (hI : I.IsNonincreasingConsecutive)
include hI

theorem length_antitone : Antitone (intervalLength I) :=
  Fin.antitone_iff_succ_le.mpr fun i => hI.2.2.1 i

theorem length_pos (j : Fin (N + 1)) : 0 < intervalLength I j :=
  lt_of_lt_of_le hI.2.2.2 (length_antitone hI (Fin.le_last j))

theorem left_monotone : Monotone I.left := by
  rw [Fin.monotone_iff_le_succ]
  intro i
  rw [hI.2.1 i]
  exact I.left_le_right i.castSucc

/-- The intervals are consecutive: `r_i ≤ ℓ_j` for `i < j`. -/
theorem right_le_left {i j : Fin (N + 1)} (hij : i < j) : I.right i ≤ I.left j := by
  have hiN : i.val < N := by
    have := j.isLt
    rw [Fin.lt_def] at hij
    omega
  have hi : (⟨i.val, hiN⟩ : Fin N).castSucc = i := Fin.ext rfl
  rw [← hi, ← hI.2.1 ⟨i.val, hiN⟩]
  apply left_monotone hI
  rw [Fin.le_iff_val_le_val]
  rw [Fin.lt_def] at hij
  simp only [Fin.val_succ]
  omega

/-- Interval `i` contributes `d_i` at realizations `j ≤ i` and nothing at `j > i`. -/
theorem value_eq (i j : Fin (N + 1)) :
    I.value i j = I.left j + if j ≤ i then intervalLength I i else 0 := by
  unfold IntervalInstance.value intervalLength
  split_ifs with hji
  · rw [max_eq_left (left_monotone hI hji),
      max_eq_right (sub_nonneg.mpr (I.left_le_right i))]
  · have hij : i < j := lt_of_not_ge hji
    have h1 := right_le_left hI hij
    rw [max_eq_right (left_monotone hI hij.le), max_eq_left (by linarith), add_zero]

/-- Every fixed interval `i` has expected value `E[ℓ_j] + d_i Σ_{j ≤ i} p_j`. -/
theorem expectedValue_eq_cumulative (i : Fin (N + 1)) :
    ∑ j, I.prob j * I.value i j =
      ∑ j, I.prob j * I.left j + intervalLength I i * ∑ j ∈ Finset.Iic i, I.prob j := by
  simp_rw [value_eq hI, mul_add, Finset.sum_add_distrib]
  congr 1
  rw [sum_Iic_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

/-- The equalizing distribution (5): `p` is equalizing if and only if
`Σ_{j ≤ i} p_j = d_N / d_i` for every `i`. -/
theorem isEqualizing_iff : I.IsEqualizing ↔
    ∀ i, ∑ j ∈ Finset.Iic i, I.prob j = intervalLength I (Fin.last N) / intervalLength I i := by
  have hlast : ∑ j ∈ Finset.Iic (Fin.last N), I.prob j = 1 := by
    rw [sum_Iic_eq]
    simp only [Fin.le_last, if_true]
    exact I.prob_sum
  constructor
  · intro hE i
    have h := hE i (Fin.last N)
    rw [expectedValue_eq_cumulative hI, expectedValue_eq_cumulative hI, hlast] at h
    rw [eq_div_iff (length_pos hI i).ne']
    linear_combination h
  · intro h i i'
    rw [expectedValue_eq_cumulative hI, expectedValue_eq_cumulative hI, h i, h i', mul_div_assoc',
      mul_div_cancel_left₀ _ (length_pos hI i).ne', mul_div_assoc',
      mul_div_cancel_left₀ _ (length_pos hI i').ne']

end Consecutive

end ConsistentSubmodular.Chains
