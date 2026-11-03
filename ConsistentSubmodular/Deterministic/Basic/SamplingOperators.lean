module

public import ConsistentSubmodular.Deterministic.Basic.FiniteExpectation
public import ConsistentSubmodular.Deterministic.Basic.Model

@[expose] public section

/-! Finite subset sampling operators for an elementary physical lift. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

def subsetWeight (U : Finset ι) (p : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ i ∈ S, p i) * ∏ i ∈ U \ S, (1 - p i)

def sampleExpectation (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, subsetWeight U p S * v S

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

theorem subsetWeight_nonnegative (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {S : Finset ι} (hS : S ⊆ U) :
    0 ≤ subsetWeight U p S := by
  exact mul_nonneg (Finset.prod_nonneg (fun i hi => (hp i (hS hi)).1))
    (Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hp i (Finset.mem_sdiff.mp hi).1).2))

theorem sampleExpectation_mono (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S ≤ w S) : sampleExpectation U p v ≤ sampleExpectation U p w := by
  apply Finset.sum_le_sum
  intro S hS
  have hSU := Finset.mem_powerset.mp hS
  exact mul_le_mul_of_nonneg_left (h S hSU) (subsetWeight_nonnegative U p hp hSU)

@[simp] theorem sampleExpectation_empty (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation ∅ p v = v ∅ := by simp [sampleExpectation, subsetWeight]

theorem sampleExpectation_add (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S + w S) = sampleExpectation U p v + sampleExpectation U p w := by
  simp only [sampleExpectation, mul_add, Finset.sum_add_distrib]

theorem sampleExpectation_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    sampleExpectation U p (fun S => c * v S) = c * sampleExpectation U p v := by
  simp only [sampleExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem sampleExpectation_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation (insert e U) p v =
      (1 - p e) * sampleExpectation U p v + p e * sampleExpectation U p (fun S => v (insert e S)) := by
  unfold sampleExpectation
  rw [Finset.sum_powerset_insert he]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    have hSU := Finset.mem_powerset.mp hS
    have heS : e ∉ S := fun h => he (hSU h)
    have hd : (insert e U) \ S = insert e (U \ S) := by
      ext i
      by_cases hie : i = e <;> simp [hie, heS]
    unfold subsetWeight
    rw [hd, Finset.prod_insert (by simp [he])]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    have hSU := Finset.mem_powerset.mp hS
    have heS : e ∉ S := fun h => he (hSU h)
    have hd : (insert e U) \ insert e S = U \ S := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, hn⟩
        · exact (hn (Or.inl hi)).elim
        · exact ⟨hi, fun h => hn (Or.inr h)⟩
      · rintro ⟨hi, hn⟩
        exact ⟨Or.inr hi, by rintro (rfl | h); exact he hi; exact hn h⟩
    unfold subsetWeight
    rw [hd, Finset.prod_insert heS]
    ring

theorem sampleExpectation_congr (U : Finset ι) (p : ι → ℝ) {v w : Finset ι → ℝ}
    (h : ∀ S ⊆ U, v S = w S) : sampleExpectation U p v = sampleExpectation U p w := by
  exact Finset.sum_congr rfl (fun S hS => by rw [h S (Finset.mem_powerset.mp hS)])

theorem sampleExpectation_nonnegative (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ}
    (hv : ∀ S ⊆ U, 0 ≤ v S) : 0 ≤ sampleExpectation U p v := by
  exact Finset.sum_nonneg (fun S hS => mul_nonneg
    (subsetWeight_nonnegative U p hp (Finset.mem_powerset.mp hS)) (hv S (Finset.mem_powerset.mp hS)))

@[simp] theorem sampleExpectation_const (U : Finset ι) (p : ι → ℝ) (c : ℝ) :
    sampleExpectation U p (fun _ => c) = c := by
  unfold sampleExpectation subsetWeight
  rw [← Finset.sum_mul, ← Finset.prod_add]
  simp

theorem sampleExpectation_sub (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) :
    sampleExpectation U p (fun S => v S - w S) = sampleExpectation U p v - sampleExpectation U p w := by
  simp only [sampleExpectation, mul_sub, Finset.sum_sub_distrib]

def sampleAdd (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) : ℝ :=
  sampleExpectation U p (fun S => v (B ∪ S))

@[simp] theorem sampleAdd_empty (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd ∅ p v B = v B := by simp [sampleAdd]

theorem sampleAdd_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd (insert e U) p v B =
      (1 - p e) * sampleAdd U p v B + p e * sampleAdd U p v (insert e B) := by
  unfold sampleAdd
  rw [sampleExpectation_insert U he]
  simp only [Finset.union_insert, Finset.insert_union]

theorem sampleAdd_add (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (fun S => v S + w S) B = sampleAdd U p v B + sampleAdd U p w B :=
  sampleExpectation_add U p _ _

theorem sampleAdd_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (fun S => c * v S) B = c * sampleAdd U p v B :=
  sampleExpectation_mul U p c _

theorem sampleAdd_insert_base (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ)
    (B : Finset ι) (e : ι) :
    sampleAdd U p (fun S => v (insert e S)) B = sampleAdd U p v (insert e B) := by
  simp only [sampleAdd, Finset.insert_union]

theorem sampleAdd_comm (U V : Finset ι) (p q : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (sampleAdd V q v) B = sampleAdd V q (sampleAdd U p v) B := by
  unfold sampleAdd sampleExpectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.union_right_comm B S T]
  ring

/-- Combining independent physical samples takes the union of their inclusion
probabilities. The identity is purely finite polynomial algebra. -/
theorem sampleAdd_union_probabilities (U : Finset ι) (p q : ι → ℝ)
    (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (sampleAdd U q v) B =
      sampleAdd U (fun i => p i + q i - p i * q i) v B := by
  induction U using Finset.induction_on generalizing B with
  | empty => simp
  | @insert e U he ih =>
    rw [sampleAdd_insert U he, sampleAdd_insert U he]
    have hfun : sampleAdd (insert e U) q v =
        fun S => (1 - q e) * sampleAdd U q v S + q e * sampleAdd U q v (insert e S) := by
      funext S
      exact sampleAdd_insert U he q v S
    rw [hfun]
    simp only [sampleAdd_add, sampleAdd_mul, sampleAdd_insert_base, ih, Finset.insert_idem]
    ring

namespace Objective

variable {n : ℕ} (f : Objective n)

/-- Independent uniform thinning of a core dominates its all-or-nothing
mixture, including an arbitrary contracted physical buffer. -/
theorem uniform_sample_chord (A B : Finset (Fin n)) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1 - p) * f.value B + p * f.value (B ∪ A) ≤ sampleAdd A (fun _ => p) f.value B := by
  induction A using Finset.induction_on generalizing B with
  | empty => simp only [sampleAdd_empty, Finset.union_empty]; nlinarith
  | @insert e A he ih =>
    rw [sampleAdd_insert A he]
    have h0 := mul_le_mul_of_nonneg_left (ih B) (sub_nonneg.mpr hp')
    have h1 := mul_le_mul_of_nonneg_left (ih (insert e B)) hp
    have hs := f.submodular (B ∪ A) (insert e B)
    have hB : B ⊆ (B ∪ A) ∩ insert e B := by
      exact Finset.subset_inter Finset.subset_union_left (Finset.subset_insert e B)
    have hb := f.monotone _ _ hB
    have hu : (B ∪ A) ∪ insert e B = B ∪ insert e A := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hu' : insert e B ∪ A = B ∪ insert e A := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hu] at hs
    have hmargin : 0 ≤ f.value (B ∪ A) + f.value (insert e B) - f.value B - f.value (B ∪ insert e A) := by linarith
    have hweighted := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) hmargin
    rw [hu'] at h1
    nlinarith only [h0, h1, hweighted]

end Objective

end ConsistentSubmodular
