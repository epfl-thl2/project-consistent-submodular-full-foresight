module

public import ConsistentSubmodular.Deterministic.Basic.Model
public import ConsistentSubmodular.Deterministic.Basic.FiniteExpectation

@[expose] public section

/-!
Compatible type objectives induced by arbitrary overlapping physical cores,
the pool and terminal values of their least compatible completion, the
multilinear value of a type mixture, and the safety of paths. The reduction
(Theorem 5) rounds these values; the proof of Theorem 7 splits atoms and
triangularizes profiles in later steps.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {n d : ℕ} (f : Objective n)

/-- Contract a buffer and replace each type by its physical core. Core overlap
and repeated identical cores are both allowed. -/
def onTypes (cores : Fin d → Finset (Fin n)) (Q : Finset (Fin n)) : Objective d where
  value I := f.value (Q ∪ I.biUnion cores)
  nonnegative I := f.nonnegative _
  monotone I J hIJ := f.monotone _ _
    (Finset.union_subset_union_right (Finset.biUnion_subset_biUnion_of_subset_left cores hIJ))
  submodular I J := by
    have hs := f.submodular (Q ∪ I.biUnion cores) (Q ∪ J.biUnion cores)
    have hsub : Q ∪ (I ∩ J).biUnion cores ⊆
        (Q ∪ I.biUnion cores) ∩ (Q ∪ J.biUnion cores) := by
      apply Finset.subset_inter
      · exact Finset.union_subset_union_right
          (Finset.biUnion_subset_biUnion_of_subset_left cores Finset.inter_subset_left)
      · exact Finset.union_subset_union_right
          (Finset.biUnion_subset_biUnion_of_subset_left cores Finset.inter_subset_right)
    have hm := f.monotone _ _ hsub
    have hu : (Q ∪ I.biUnion cores) ∪ (Q ∪ J.biUnion cores) =
        Q ∪ (I ∪ J).biUnion cores := by
      rw [Finset.union_biUnion]
      ext e
      simp only [Finset.mem_union]
      tauto
    rw [hu] at hs
    linarith

@[simp] theorem onTypes_empty (cores : Fin d → Finset (Fin n)) (Q : Finset (Fin n)) :
    (f.onTypes cores Q).value ∅ = f.value Q := by simp [onTypes]

@[simp] theorem onTypes_singleton (cores : Fin d → Finset (Fin n))
    (Q : Finset (Fin n)) (i : Fin d) :
    (f.onTypes cores Q).value {i} = f.value (Q ∪ cores i) := by simp [onTypes]

end Objective

/-- Time increases values and decreases every fixed-context type marginal. -/
structure CompatibleProfile (d : ℕ) where
  objective : ℕ → Objective d
  values_increase : ∀ s t, s ≤ t → ∀ I, (objective s).value I ≤ (objective t).value I
  marginals_decrease : ∀ s t, s ≤ t → ∀ I J, I ⊆ J →
    (objective t).value J - (objective t).value I ≤
      (objective s).value J - (objective s).value I

namespace CompatibleProfile

variable {n d : ℕ}

def fromPhysical (f : Objective n) (cores : Fin d → Finset (Fin n))
    (Q : ℕ → Finset (Fin n)) (hQ : Monotone Q) : CompatibleProfile d where
  objective t := f.onTypes cores (Q t)
  values_increase s t hst I := f.monotone _ _ (Finset.union_subset_union_left (hQ hst))
  marginals_decrease s t hst I J hIJ := by
    have hcore := Finset.biUnion_subset_biUnion_of_subset_left cores hIJ
    have h := f.diminishing_returns (A := Q s ∪ I.biUnion cores)
      (B := Q t ∪ I.biUnion cores) (Finset.union_subset_union_left (hQ hst))
      (J.biUnion cores)
    have hu (u : ℕ) : (Q u ∪ I.biUnion cores) ∪ J.biUnion cores = Q u ∪ J.biUnion cores := by
      rw [Finset.union_assoc, Finset.union_eq_right.mpr hcore]
    simpa only [Objective.onTypes, hu] using h

variable (P : CompatibleProfile d)

def baseline (t : ℕ) : ℝ := (P.objective t).value ∅

def residualOn (t : ℕ) (I : Finset (Fin d)) : ℝ :=
  (P.objective t).value I - P.baseline t

def residual (t : ℕ) (i : Fin d) : ℝ := P.residualOn t {i}

def loss (t : ℕ) (i : Fin d) : ℝ := P.residual t i - P.residual (t + 1) i

theorem residualOn_nonnegative (t : ℕ) (I : Finset (Fin d)) : 0 ≤ P.residualOn t I := by
  exact sub_nonneg.mpr ((P.objective t).monotone ∅ I (Finset.empty_subset _))

theorem residualOn_antitone {s t : ℕ} (hst : s ≤ t) (I : Finset (Fin d)) :
    P.residualOn t I ≤ P.residualOn s I :=
  P.marginals_decrease s t hst ∅ I (Finset.empty_subset _)

theorem loss_nonnegative (t : ℕ) (i : Fin d) : 0 ≤ P.loss t i :=
  sub_nonneg.mpr (P.residualOn_antitone (Nat.le_succ t) {i})

end CompatibleProfile

/-- The finite maximum, with zero for the empty family. All uses below have
nonnegative entries, so adjoining the empty maximum causes no ambiguity. -/
def finiteMaximum {ι : Type*} (I : Finset ι) (g : ι → ℝ) : ℝ :=
  if h : I.Nonempty then g (Classical.choose (I.exists_max_image g h)) else 0

theorem finiteMaximum_le {ι : Type*} {I : Finset ι} {g : ι → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (h : ∀ i ∈ I, g i ≤ a) : finiteMaximum I g ≤ a := by
  classical
  by_cases hI : I.Nonempty
  · rw [finiteMaximum, dif_pos hI]
    exact h _ (Classical.choose_spec (I.exists_max_image g hI)).1
  · simp [finiteMaximum, hI, ha]

theorem le_finiteMaximum {ι : Type*} {I : Finset ι} {g : ι → ℝ}
    {i : ι} (hi : i ∈ I) : g i ≤ finiteMaximum I g := by
  classical
  have hI : I.Nonempty := ⟨i, hi⟩
  rw [finiteMaximum, dif_pos hI]
  exact (Classical.choose_spec (I.exists_max_image g hI)).2 i hi

theorem finiteMaximum_nonnegative {ι : Type*} {I : Finset ι} {g : ι → ℝ}
    (h : ∀ i ∈ I, 0 ≤ g i) : 0 ≤ finiteMaximum I g := by
  classical
  by_cases hI : I.Nonempty
  · rw [finiteMaximum, dif_pos hI]
    exact h _ (Classical.choose_spec (I.exists_max_image g hI)).1
  · simp [finiteMaximum, hI]

@[simp] theorem finiteMaximum_singleton {ι : Type*} (i : ι) (g : ι → ℝ)
    (hg : 0 ≤ g i) : finiteMaximum {i} g = g i := by
  classical
  exact le_antisymm (finiteMaximum_le hg (by simp)) (le_finiteMaximum (Finset.mem_singleton_self i))

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

def poolValue (t : ℕ) (I : Finset (Fin d)) : ℝ := finiteMaximum I (P.loss t)

def terminalValue (m : ℕ) (I : Finset (Fin d)) : ℝ := finiteMaximum I (P.residual m)

theorem poolValue_le_residual_drop (t : ℕ) (I : Finset (Fin d)) :
    P.poolValue t I ≤ P.residualOn t I - P.residualOn (t + 1) I := by
  apply finiteMaximum_le
  · exact sub_nonneg.mpr (P.residualOn_antitone (Nat.le_succ t) I)
  · intro i hi
    have h := P.marginals_decrease t (t + 1) (Nat.le_succ t) {i} I
      (Finset.singleton_subset_iff.mpr hi)
    dsimp [loss, residual, residualOn, baseline]
    linarith

theorem terminalValue_le_residual (m : ℕ) (I : Finset (Fin d)) :
    P.terminalValue m I ≤ P.residualOn m I := by
  apply finiteMaximum_le (P.residualOn_nonnegative m I)
  intro i hi
  exact sub_le_sub_right ((P.objective m).monotone {i} I
    (Finset.singleton_subset_iff.mpr hi)) _

/-- Each baseline increment pays for the full expiring pool. -/
theorem pool_total_le_baseline_increment (t : ℕ) :
    P.poolValue t Finset.univ ≤ P.baseline (t + 1) - P.baseline t := by
  apply finiteMaximum_le
  · exact sub_nonneg.mpr (P.values_increase t (t + 1) (Nat.le_succ t) ∅)
  · intro i _
    have h := P.values_increase t (t + 1) (Nat.le_succ t) {i}
    dsimp [loss, residual, residualOn, baseline]
    linarith

end CompatibleProfile

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

/-- The value of a type mixture at stage `t`: the expectation of the profile's
objective under independent type samples. -/
def multilinearValue (t : ℕ) (p : Point m) : ℝ := finiteExpectation p (P.objective t).value

/-- Safety of a polygonal path at stage `t` and level `level`: every point lies in
the simplex and has multilinear value at least `level`. -/
def SafePath (t : ℕ) (level : ℝ) (γ : PolygonalPath m) : Prop :=
  (∀ j, IsSimplex (γ.node j) ∧ level ≤ P.multilinearValue t (γ.node j)) ∧
  ∀ (j : Fin γ.pieces) (x : ℝ), 0 ≤ x → x ≤ 1 →
    IsSimplex (mix (γ.node j.castSucc) (γ.node j.succ) x) ∧
    level ≤ P.multilinearValue t (mix (γ.node j.castSucc) (γ.node j.succ) x)

end CompatibleProfile

end ConsistentSubmodular
