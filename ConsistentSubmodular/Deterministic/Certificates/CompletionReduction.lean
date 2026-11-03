module

public import ConsistentSubmodular.Deterministic.Certificates.Triangularization
public import ConsistentSubmodular.Deterministic.Basic.FiniteExpectation
public import ConsistentSubmodular.Deterministic.Certificates.AtomicFacts

@[expose] public section

/-! Pointwise transfer from a compatible profile to its finite triangular atomic
completion, with baseline restoration at every checkpoint and path point. The
final theorem of this file assumes the finite checkpoint theorem. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))
variable (hinit : P.residual 0 0 = 1)
variable (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t)

def atomicCompletion := (P.toTriangularArray hinit hopt).toAtomic

theorem atomicCompletion_canonical : (P.atomicCompletion hinit hopt).Canonical :=
  (P.toTriangularArray hinit hopt).toAtomic_canonical

theorem atomicCompletion_designated (t : Fin (m + 1)) :
    (P.atomicCompletion hinit hopt).designated t = P.residual t.val t := by
  unfold atomicCompletion AtomicProfile.designated
  rw [TriangularArray.atomic_residual]
  exact P.triangularLength_designated t

theorem atomicCompletion_baseline_le (t : Fin (m + 1)) :
    (P.atomicCompletion hinit hopt).baseline t ≤ P.baseline t.val := by
  unfold atomicCompletion
  rw [TriangularArray.atomic_baseline]
  exact P.triangular_baseline_le t

/-- Adding back the exact baseline slack gives pointwise Boolean domination. -/
theorem atomicCompletion_unionValue_le (t : Fin (m + 1)) (I : Finset (Fin (m + 1))) :
    (P.atomicCompletion hinit hopt).unionValue t I +
      (P.baseline t.val - (P.atomicCompletion hinit hopt).baseline t) ≤
      (P.objective t.val).value I := by
  have hres := P.triangular_union_tail_le I t
  unfold AtomicProfile.unionValue atomicCompletion
  rw [TriangularArray.atomic_unionValue]
  change (P.toTriangularArray hinit hopt).toAtomic.baseline t +
      (∑ j, if t ≤ j then finiteMaximum I (fun i => P.triangularLength i j) else 0) +
      (P.baseline t.val - (P.toTriangularArray hinit hopt).toAtomic.baseline t) ≤ _
  dsimp [residualOn] at hres
  linarith

/-- Finite expectation preserves the completion inequality on the entire cube. -/
theorem atomicCompletion_multilinear_le (t : Fin (m + 1)) (p : Point m)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (P.atomicCompletion hinit hopt).value t p +
      (P.baseline t.val - (P.atomicCompletion hinit hopt).baseline t) ≤
      P.multilinearValue t.val p := by
  have h := finiteExpectation_mono p hp (P.atomicCompletion_unionValue_le hinit hopt t)
  rw [finiteExpectation_add, finiteExpectation_const,
    ← AtomicProfile.value_eq_expectation] at h
  exact h

/-- Baseline restoration incurs no additional approximation factor. -/
theorem atomicCompletion_approximation_transfer (t : Fin (m + 1)) (p : Point m)
    (hp : IsSimplex p) {α : ℝ} (hα : α ≤ 1)
    (hgood : α * (P.atomicCompletion hinit hopt).benchmark t ≤
      (P.atomicCompletion hinit hopt).value t p) :
    α * (P.objective t.val).value {t} ≤ P.multilinearValue t.val p := by
  have hdom := P.atomicCompletion_multilinear_le hinit hopt t p
    (fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩)
  have hbase := P.atomicCompletion_baseline_le hinit hopt t
  have hmul := mul_le_of_le_one_left (sub_nonneg.mpr hbase) hα
  unfold AtomicProfile.benchmark at hgood
  rw [P.atomicCompletion_designated hinit hopt t] at hgood
  dsimp [residual, residualOn] at hgood
  nlinarith

theorem atomicCompletion_path_transfer (t : Fin (m + 1)) (γ : PolygonalPath m)
    {α : ℝ} (hα : α ≤ 1)
    (hγ : ConsistentSubmodular.SafePath (P.atomicCompletion hinit hopt) t
      (α * (P.atomicCompletion hinit hopt).benchmark t) γ) :
    P.SafePath t.val (α * (P.objective t.val).value {t}) γ := by
  constructor
  · intro j
    exact ⟨(hγ.1 j).1, P.atomicCompletion_approximation_transfer hinit hopt t _ (hγ.1 j).1 hα (hγ.1 j).2⟩
  · intro j x hx hx'
    have h := hγ.2 j x hx hx'
    exact ⟨h.1, P.atomicCompletion_approximation_transfer hinit hopt t _ h.1 hα h.2⟩

include hinit hopt in
/-- The normalized positive-scale transfer preserves the common checkpoint,
prescribed endpoints, zero-piece safety, and total affine-piece budget. -/
theorem checkpoint_of_finite_checkpoint (hfinite : FiniteCheckpointGoal) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (P.objective t.val).value {t} ≤ P.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      P.SafePath 0 ((3 : ℝ) / 4 * (P.objective 0).value {0}) entry ∧
      P.SafePath m ((3 : ℝ) / 4 * (P.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  obtain ⟨p, entry, exit, hp, hsupport, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    hfinite m _ (P.atomicCompletion hinit hopt) (P.atomicCompletion_canonical hinit hopt)
  have hbenchmark0 : (P.atomicCompletion hinit hopt).benchmark 0 = 1 := by
    unfold AtomicProfile.benchmark
    rw [P.atomicCompletion_designated hinit hopt]
    simp [AtomicProfile.baseline, hinit]
  refine ⟨p, entry, exit, hp, hsupport, ?_, he0, he1, hx0, hx1, ?_, ?_, hpieces⟩
  · intro t
    exact P.atomicCompletion_approximation_transfer hinit hopt t p hp (by norm_num) (hstage t)
  · apply P.atomicCompletion_path_transfer hinit hopt 0 entry (by norm_num : (3 : ℝ) / 4 ≤ 1)
    simpa only [hbenchmark0, mul_one] using hentry
  · exact P.atomicCompletion_path_transfer hinit hopt (Fin.last m) exit (by norm_num) hexit

end CompatibleProfile

end ConsistentSubmodular
