module

public import ConsistentSubmodular.Deterministic.Basic.SamplingOperators
public import ConsistentSubmodular.Deterministic.Basic.PhysicalMap
public import ConsistentSubmodular.Deterministic.Basic.CompatibleProfiles

@[expose] public section

/-!
Physical multilinear lift by independent block-coin replacement: inequality
(21) of Lemma B.2 (Appendix B.2.1). This is an elementary equivalent of the
separate-concavity argument in the paper's proof.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_congr_prob (U : Finset ι) (p q : ι → ℝ)
    (hpq : ∀ i ∈ U, p i = q i) (v : Finset ι → ℝ) :
    sampleExpectation U p v = sampleExpectation U q v := by
  apply Finset.sum_congr rfl
  intro S hS
  have hSU := Finset.mem_powerset.mp hS
  congr 1
  unfold subsetWeight
  congr 1
  · exact Finset.prod_congr rfl (fun i hi => hpq i (hSU hi))
  · exact Finset.prod_congr rfl (fun i hi => by rw [hpq i (Finset.mem_sdiff.mp hi).1])

theorem sampleExpectation_inter_zero (U V : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    sampleExpectation V p v = sampleExpectation (V ∩ U) p v := by
  induction V using Finset.induction_on generalizing v with
  | empty => simp
  | @insert e V he ih =>
    by_cases heU : e ∈ U
    · have hinter : insert e V ∩ U = insert e (V ∩ U) := by
        ext i
        by_cases hie : i = e <;> simp [hie, heU]
      rw [hinter, sampleExpectation_insert V he,
        sampleExpectation_insert (V ∩ U) (by simp [he]), ih, ih]
    · have hinter : insert e V ∩ U = V ∩ U := by
        ext i
        by_cases hie : i = e <;> simp [hie, heU]
      rw [hinter, sampleExpectation_insert V he, hp e heU]
      simp [ih]

theorem sampleAdd_mask [Fintype ι] (U : Finset ι) (p : ι → ℝ)
    (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd Finset.univ (fun i => if i ∈ U then p i else 0) v B = sampleAdd U p v B := by
  unfold sampleAdd
  rw [sampleExpectation_inter_zero U Finset.univ _ (fun i hi => by simp [hi]), Finset.univ_inter]
  exact sampleExpectation_congr_prob U _ p (fun i hi => by simp [hi]) _

namespace Objective

variable {n : ℕ} (f : Objective n)

/-- Contracting a finite independent sample preserves all objective axioms. -/
def sampled (U : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) : Objective n where
  value B := sampleAdd U p f.value B
  nonnegative B := by
    apply Finset.sum_nonneg
    intro S hS
    exact mul_nonneg (subsetWeight_nonnegative U p hp (Finset.mem_powerset.mp hS)) (f.nonnegative _)
  monotone B C hBC := sampleExpectation_mono U p hp (fun S _ =>
    f.monotone _ _ (Finset.union_subset_union_left hBC))
  submodular B C := by
    have hpoint (S : Finset (Fin n)) : f.value ((B ∪ C) ∪ S) + f.value ((B ∩ C) ∪ S) ≤
        f.value (B ∪ S) + f.value (C ∪ S) := by
      have hU : (B ∪ S) ∪ (C ∪ S) = (B ∪ C) ∪ S := by ext i; simp only [Finset.mem_union]; tauto
      have hI : (B ∪ S) ∩ (C ∪ S) = (B ∩ C) ∪ S := by ext i; simp only [Finset.mem_union, Finset.mem_inter]; tauto
      simpa only [hU, hI] using f.submodular (B ∪ S) (C ∪ S)
    have h := sampleExpectation_mono U p hp (fun S _ => hpoint S)
    simpa only [sampleExpectation_add] using h

theorem sampleAdd_mono_probability (U : Finset (Fin n)) (p q : Fin n → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (hq : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1)
    (hpq : ∀ i ∈ U, p i ≤ q i) (B : Finset (Fin n)) :
    sampleAdd U p f.value B ≤ sampleAdd U q f.value B := by
  induction U using Finset.induction_on generalizing B with
  | empty => simp
  | @insert e U he ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    have hqU : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hpqU : ∀ i ∈ U, p i ≤ q i := fun i hi => hpq i (Finset.mem_insert_of_mem hi)
    rw [sampleAdd_insert U he, sampleAdd_insert U he]
    have h0 := mul_le_mul_of_nonneg_left (ih hpU hqU hpqU B)
      (sub_nonneg.mpr (hp e (Finset.mem_insert_self e U)).2)
    have h1 := mul_le_mul_of_nonneg_left (ih hpU hqU hpqU (insert e B))
      (hp e (Finset.mem_insert_self e U)).1
    have hm := (f.sampled U q hqU).monotone B (insert e B) (Finset.subset_insert e B)
    have hdiff := mul_nonneg (sub_nonneg.mpr (hpq e (Finset.mem_insert_self e U))) (sub_nonneg.mpr hm)
    change 0 ≤ (q e - p e) * (sampleAdd U q f.value (insert e B) - sampleAdd U q f.value B) at hdiff
    nlinarith only [h0, h1, hdiff]

end Objective

variable {n : ℕ}

def unionProbability (cores : ι → Finset (Fin n)) (U : Finset ι) (p : ι → ℝ) (e : Fin n) : ℝ :=
  1 - ∏ i ∈ U, if e ∈ cores i then 1 - p i else 1

omit [DecidableEq ι] in
@[simp] theorem unionProbability_empty (cores : ι → Finset (Fin n)) (p : ι → ℝ) (e : Fin n) :
    unionProbability cores ∅ p e = 0 := by simp [unionProbability]

theorem unionProbability_insert (cores : ι → Finset (Fin n)) (U : Finset ι)
    {i : ι} (hi : i ∉ U) (p : ι → ℝ) (e : Fin n) :
    unionProbability cores (insert i U) p e = unionProbability cores U p e +
      (if e ∈ cores i then p i else 0) - unionProbability cores U p e * (if e ∈ cores i then p i else 0) := by
  unfold unionProbability
  rw [Finset.prod_insert hi]
  split_ifs <;> ring

omit [DecidableEq ι] in
theorem unionProbability_mem_unitInterval (cores : ι → Finset (Fin n)) (U : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (e : Fin n) :
    0 ≤ unionProbability cores U p e ∧ unionProbability cores U p e ≤ 1 := by
  have hnonneg : 0 ≤ ∏ i ∈ U, if e ∈ cores i then 1 - p i else 1 := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact sub_nonneg.mpr (hp i hi).2
    · norm_num
  have hle : (∏ i ∈ U, if e ∈ cores i then 1 - p i else 1) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      split_ifs
      · exact sub_nonneg.mpr (hp i hi).2
      · norm_num
    · intro i hi
      split_ifs
      · linarith [(hp i hi).1]
      · rfl
  dsimp [unionProbability]
  constructor <;> linarith

theorem unionProbability_le_sum (cores : ι → Finset (Fin n)) (U : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (e : Fin n) :
    unionProbability cores U p e ≤ ∑ i ∈ U, if e ∈ cores i then p i else 0 := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert i U hi ih =>
    have hpU : ∀ j ∈ U, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    rw [unionProbability_insert cores U hi, Finset.sum_insert hi]
    have hbase := (unionProbability_mem_unitInterval cores U p hpU e).1
    have hpi : 0 ≤ (if e ∈ cores i then p i else 0) := by
      split_ifs
      · exact (hp i (Finset.mem_insert_self i U)).1
      · rfl
    have hmul := mul_nonneg hbase hpi
    have hrec := ih hpU
    linarith

/-- Replacing every common core coin by independent element coins can only
increase expected submodular value. Overlaps and repeated cores are allowed. -/
theorem type_expectation_le_independent_union (f : Objective n)
    (cores : ι → Finset (Fin n)) (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (B : Finset (Fin n)) :
    sampleExpectation U p (fun I => f.value (B ∪ I.biUnion cores)) ≤
      sampleAdd Finset.univ (unionProbability cores U p) f.value B := by
  induction U using Finset.induction_on generalizing B with
  | empty =>
    simp only [sampleExpectation_empty, Finset.biUnion_empty, Finset.union_empty]
    have hzero : sampleAdd Finset.univ (fun _ : Fin n => 0) f.value B = f.value B := by
      simpa using sampleAdd_mask (∅ : Finset (Fin n)) (fun _ => 0) f.value B
    have hqzero : unionProbability cores ∅ p = fun _ => 0 := funext (unionProbability_empty cores p)
    rw [hqzero]
    exact hzero.ge
  | @insert i U hi ih =>
    have hpU : ∀ j ∈ U, 0 ≤ p j ∧ p j ≤ 1 := fun j hj => hp j (Finset.mem_insert_of_mem hj)
    have hpi := hp i (Finset.mem_insert_self i U)
    have hq : ∀ e ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ unionProbability cores U p e ∧ unionProbability cores U p e ≤ 1 :=
      fun e _ => unionProbability_mem_unitInterval cores U p hpU e
    let g := f.sampled Finset.univ (unionProbability cores U p) hq
    rw [sampleExpectation_insert U hi]
    have hfun : (fun I : Finset ι => f.value (B ∪ (insert i I).biUnion cores)) =
        (fun I : Finset ι => f.value ((B ∪ cores i) ∪ I.biUnion cores)) := by
      funext I
      rw [Finset.biUnion_insert, Finset.union_assoc]
    rw [hfun]
    have h0 := mul_le_mul_of_nonneg_left (ih hpU B) (sub_nonneg.mpr hpi.2)
    have h1 := mul_le_mul_of_nonneg_left (ih hpU (B ∪ cores i)) hpi.1
    have hchord := g.uniform_sample_chord (cores i) B (p i) hpi.1 hpi.2
    change (1 - p i) * sampleAdd Finset.univ (unionProbability cores U p) f.value B +
        p i * sampleAdd Finset.univ (unionProbability cores U p) f.value (B ∪ cores i) ≤
        sampleAdd (cores i) (fun _ => p i) (sampleAdd Finset.univ (unionProbability cores U p) f.value) B at hchord
    have hphysical : sampleAdd (cores i) (fun _ => p i)
        (sampleAdd Finset.univ (unionProbability cores U p) f.value) B =
        sampleAdd Finset.univ (unionProbability cores (insert i U) p) f.value B := by
      rw [sampleAdd_comm]
      have hmask : sampleAdd (cores i) (fun _ => p i) f.value =
          sampleAdd Finset.univ (fun e => if e ∈ cores i then p i else 0) f.value := by
        funext C
        exact (sampleAdd_mask (cores i) (fun _ => p i) f.value C).symm
      rw [hmask, sampleAdd_union_probabilities]
      congr 1
      funext e
      exact (unionProbability_insert cores U hi p e).symm
    rw [hphysical] at hchord
    linarith only [h0, h1, hchord]

/-- Physical multilinear lift on the whole type subprobability simplex. -/
theorem physical_multilinear_lift {m : ℕ} (f : Objective n)
    (cores : Fin (m + 1) → Finset (Fin n)) (B : Finset (Fin n)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) ≤ 1) :
    finiteExpectation p (f.onTypes cores B).value ≤
      finiteExpectation (physicalProbability cores p) (fun S => f.value (B ∪ S)) := by
  have hpcube : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := by
    intro i
    exact ⟨hp i, (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans hmass⟩
  have hqcube : ∀ e ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ unionProbability cores Finset.univ p e ∧ unionProbability cores Finset.univ p e ≤ 1 :=
    fun e _ => unionProbability_mem_unitInterval cores Finset.univ p (fun i _ => hpcube i) e
  have hzcube : ∀ e ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ physicalProbability cores p e ∧ physicalProbability cores p e ≤ 1 := by
    intro e _
    exact ⟨physicalProbability_nonnegative cores p hp e, (physicalProbability_le_mass cores p hp e).trans hmass⟩
  have htype := type_expectation_le_independent_union f cores Finset.univ p (fun i _ => hpcube i) B
  have hmono := f.sampleAdd_mono_probability Finset.univ (unionProbability cores Finset.univ p)
    (physicalProbability cores p) hqcube hzcube
    (fun e _ => unionProbability_le_sum cores Finset.univ p (fun i _ => hpcube i) e) B
  have h := htype.trans hmono
  simpa only [sampleAdd, sampleExpectation_univ, Objective.onTypes] using h

end ConsistentSubmodular
