module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-! Finite independent Bernoulli expectations. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliWeight (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ Sᶜ, (1 - p i)

def finiteExpectation (p : ι → ℝ) (v : Finset ι → ℝ) : ℝ :=
  ∑ S : Finset ι, bernoulliWeight p S * v S

theorem bernoulliWeight_nonnegative (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (S : Finset ι) : 0 ≤ bernoulliWeight p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => (hp i).1)
  · exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp i).2)

theorem sum_bernoulliWeight (p : ι → ℝ) : (∑ S : Finset ι, bernoulliWeight p S) = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_add]
  simp

theorem finiteExpectation_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {v w : Finset ι → ℝ} (h : ∀ S, v S ≤ w S) :
    finiteExpectation p v ≤ finiteExpectation p w := by
  exact Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (h S) (bernoulliWeight_nonnegative p hp S))

@[simp] theorem finiteExpectation_const (p : ι → ℝ) (c : ℝ) :
    finiteExpectation p (fun _ => c) = c := by
  unfold finiteExpectation
  rw [← Finset.sum_mul, sum_bernoulliWeight, one_mul]

theorem finiteExpectation_add (p : ι → ℝ) (v w : Finset ι → ℝ) :
    finiteExpectation p (fun S => v S + w S) = finiteExpectation p v + finiteExpectation p w := by
  simp only [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_mul (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    finiteExpectation p (fun S => c * v S) = c * finiteExpectation p v := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem finiteExpectation_sum {β : Type*} [Fintype β] (p : ι → ℝ)
    (v : β → Finset ι → ℝ) :
    finiteExpectation p (fun S => ∑ a, v a S) = ∑ a, finiteExpectation p (v a) := by
  simp only [finiteExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem sum_weight_disjoint (p : ι → ℝ) (L : Finset ι) :
    (∑ S : Finset ι, if Disjoint S L then bernoulliWeight p S else 0) =
      ∏ i ∈ L, (1 - p i) := by
  classical
  have hterm (S : Finset ι) :
      (if Disjoint S L then bernoulliWeight p S else 0) =
        (∏ i ∈ S, if i ∈ L then 0 else p i) * ∏ i ∈ Sᶜ, (1 - p i) := by
    by_cases hd : Disjoint S L
    · rw [if_pos hd]
      unfold bernoulliWeight
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      simp [Finset.disjoint_left.mp hd hi]
    · rw [if_neg hd]
      obtain ⟨i, hi⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hd
      have hzero : (∏ i ∈ S, if i ∈ L then (0 : ℝ) else p i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_inter.mp hi).1 (by simp [(Finset.mem_inter.mp hi).2])
      rw [hzero, zero_mul]
  simp_rw [hterm]
  rw [← Fintype.prod_add]
  have hpoint (i : ι) : (if i ∈ L then (0 : ℝ) else p i) + (1 - p i) =
      if i ∈ L then 1 - p i else 1 := by split_ifs <;> ring
  simp_rw [hpoint]
  exact Finset.prod_ite_mem_eq L (fun i => 1 - p i)

theorem finiteExpectation_hit (p : ι → ℝ) (L : Finset ι) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then 1 else 0) =
      1 - ∏ i ∈ L, (1 - p i) := by
  have hterm (S : Finset ι) : bernoulliWeight p S * (if (L ∩ S).Nonempty then 1 else 0) =
      bernoulliWeight p S - (if Disjoint S L then bernoulliWeight p S else 0) := by
    have hiff : (L ∩ S).Nonempty ↔ ¬Disjoint S L := by
      rw [Finset.inter_comm, Finset.not_disjoint_iff_nonempty_inter]
    by_cases hd : Disjoint S L <;> simp [hiff, hd]
  unfold finiteExpectation
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, sum_bernoulliWeight, sum_weight_disjoint]

theorem finiteExpectation_weighted_hit (p : ι → ℝ) (L : Finset ι) (w : ℝ) :
    finiteExpectation p (fun S => if (L ∩ S).Nonempty then w else 0) =
      w * (1 - ∏ i ∈ L, (1 - p i)) := by
  have hpoint : (fun S => if (L ∩ S).Nonempty then w else 0) =
      (fun S => w * (if (L ∩ S).Nonempty then 1 else 0)) := by
    funext S
    split_ifs <;> simp
  rw [hpoint, finiteExpectation_mul, finiteExpectation_hit]


end ConsistentSubmodular
