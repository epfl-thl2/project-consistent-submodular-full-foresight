module

public import Mathlib

@[expose] public section

/-! Elementary finite probability, Markov's inequality, and deterministic extraction. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ ω, 0 ≤ weight ω
  sum_one : (∑ ω, weight ω) = 1

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

def expect (X : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * X ω

def probability (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then μ.weight ω else 0

theorem weight_le_probability (E : Ω → Prop) (ω : Ω) (hE : E ω) :
    μ.weight ω ≤ μ.probability E := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => if E a then μ.weight a else 0)
    (fun a _ => by dsimp only; split_ifs; exact μ.nonnegative a; rfl) (Finset.mem_univ ω)
  simpa only [hE, ite_true] using h

theorem expect_mono {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : μ.expect X ≤ μ.expect Y := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonnegative ω))

theorem expect_sum {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i, X i ω) = ∑ i, μ.expect (X i) := by
  unfold expect
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem probability_eq_expect (E : Ω → Prop) [DecidablePred E] :
    μ.probability E = μ.expect (fun ω => if E ω then 1 else 0) := by
  classical
  unfold probability expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

/-- Markov's estimate, with no division or positivity convention at zero. -/
theorem markov {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) :
    a * μ.probability (fun ω => a ≤ X ω) ≤ μ.expect X := by
  classical
  unfold probability expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ X ω
  · simp only [h, ite_true]
    nlinarith [mul_nonneg (μ.nonnegative ω) (sub_nonneg.mpr h)]
  · simp only [h, ite_false, mul_zero]
    exact mul_nonneg (μ.nonnegative ω) (hX ω)

theorem exists_good_positive_of_sum_failure_lt_one {κ : Type*} [Fintype κ]
    (bad : κ → Ω → Prop) (hbad : (∑ i, μ.probability (bad i)) < 1) :
    ∃ ω, 0 < μ.weight ω ∧ ∀ i, ¬bad i ω := by
  classical
  by_contra h
  push Not at h
  have hpoint (ω : Ω) : μ.weight ω ≤ ∑ i, if bad i ω then μ.weight ω else 0 := by
    by_cases hw : 0 < μ.weight ω
    · obtain ⟨i, hi⟩ := h ω hw
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun i => if bad i ω then μ.weight ω else 0)
        (fun i _ => by dsimp only; split_ifs; exact μ.nonnegative ω; rfl) (Finset.mem_univ i)
      simpa only [hi, ite_true] using hs
    · have hz : μ.weight ω = 0 := le_antisymm (le_of_not_gt hw) (μ.nonnegative ω)
      simp [hz]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ω _ => hpoint ω)
  rw [μ.sum_one, Finset.sum_comm] at hs
  exact (not_lt_of_ge hs) hbad

end FiniteLaw

end ConsistentSubmodular
