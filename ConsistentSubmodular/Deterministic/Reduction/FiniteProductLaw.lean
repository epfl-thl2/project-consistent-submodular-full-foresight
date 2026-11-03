module

public import ConsistentSubmodular.Deterministic.Reduction.FiniteProbability
public import ConsistentSubmodular.Deterministic.Basic.SamplingOperators

@[expose] public section

/-! Finite product laws and their Bernoulli sample pushforwards. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem probability_not (E : Ω → Prop) : μ.probability (fun ω => ¬E ω) = 1 - μ.probability E := by
  classical
  unfold probability
  rw [← μ.sum_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

theorem expect_pushforward {β : Type*} [Fintype β] (F : Ω → β) (v : β → ℝ) :
    μ.expect (fun ω => v (F ω)) =
      ∑ b, μ.probability (fun ω => F ω = b) * v b := by
  classical
  unfold expect probability
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (F ω)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : κ → Type*} [∀ i, Fintype (A i)]

def product (laws : ∀ i, FiniteLaw (A i)) : FiniteLaw (∀ i, A i) where
  weight ω := ∏ i, (laws i).weight (ω i)
  nonnegative ω := Finset.prod_nonneg (fun i _ => (laws i).nonnegative (ω i))
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [(laws _).sum_one, Finset.prod_const_one]

theorem coordinate_positive_of_product_positive (laws : ∀ i, FiniteLaw (A i))
    (ω : ∀ i, A i) (h : 0 < (product laws).weight ω) (i : κ) :
    0 < (laws i).weight (ω i) := by
  classical
  apply lt_of_le_of_ne ((laws i).nonnegative (ω i))
  intro hz
  have hp : (product laws).weight ω = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz.symm
  linarith

theorem product_probability_all (laws : ∀ i, FiniteLaw (A i))
    (E : ∀ i, A i → Prop) :
    (product laws).probability (fun ω => ∀ i, E i (ω i)) = ∏ i, (laws i).probability (E i) := by
  classical
  have hpoint (ω : ∀ i, A i) :
      (if ∀ i, E i (ω i) then ∏ i, (laws i).weight (ω i) else 0) =
        ∏ i, if E i (ω i) then (laws i).weight (ω i) else 0 := by
    by_cases h : ∀ i, E i (ω i)
    · simp [h]
    · rw [if_neg h]
      push Not at h
      obtain ⟨i, hi⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])).symm
  unfold probability product
  simp only [hpoint]
  exact (Fintype.prod_sum (fun i (a : A i) => if E i a then (laws i).weight a else 0)).symm

def selectedSet (select : ∀ i, A i → Prop) (ω : ∀ i, A i) : Finset κ := by
  classical
  exact Finset.univ.filter (fun i => select i (ω i))

theorem product_selected_probability (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (S : Finset κ) :
    (product laws).probability (fun ω => selectedSet select ω = S) =
      bernoulliWeight (fun i => (laws i).probability (select i)) S := by
  classical
  have heq : (fun ω => selectedSet select ω = S) =
      (fun ω => ∀ i, if i ∈ S then select i (ω i) else ¬select i (ω i)) := by
    funext ω
    apply propext
    constructor
    · intro h i
      have hm := Finset.ext_iff.mp h i
      simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      by_cases hi : i ∈ S <;> simp [hi, hm]
    · intro h
      ext i
      have hi := h i
      simp only [selectedSet, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hiS : i ∈ S <;> simpa [hiS] using hi
  rw [heq, product_probability_all laws (fun i a => if i ∈ S then select i a else ¬select i a)]
  have hpoint (i : κ) : (laws i).probability (fun a => if i ∈ S then select i a else ¬select i a) =
      if i ∈ S then (laws i).probability (select i) else 1 - (laws i).probability (select i) := by
    by_cases hi : i ∈ S <;> simp only [hi, ite_true, ite_false, probability_not]
  simp_rw [hpoint]
  unfold bernoulliWeight
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp

/-- Any independent finite coordinate laws reproduce the Bernoulli law of
their coordinatewise inclusion events. -/
theorem product_selected_expectation (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (v : Finset κ → ℝ) :
    (product laws).expect (fun ω => v (selectedSet select ω)) =
      finiteExpectation (fun i => (laws i).probability (select i)) v := by
  rw [expect_pushforward]
  simp only [product_selected_probability, finiteExpectation]

end ConsistentSubmodular.FiniteLaw
