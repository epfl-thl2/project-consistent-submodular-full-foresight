module

public import ConsistentSubmodular.Deterministic.Basic.FiniteMaxCoverage
public import ConsistentSubmodular.Deterministic.Certificates.AtomicFacts

@[expose] public section

/-! Finite atomization of a normalized canonical triangular length array. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

structure TriangularArray (m : ℕ) where
  length : Fin (m + 1) → Fin (m + 1) → ℝ
  nonnegative : ∀ i j, 0 ≤ length i j
  triangular : ∀ i j, j < i → length i j = 0
  initial : (∑ j, length 0 j) = 1
  dominated : ∀ i t,
    (∑ j, if t ≤ j then length i j else 0) ≤
      ∑ j, if t ≤ j then length t j else 0

namespace TriangularArray

variable {m : ℕ} (M : TriangularArray m)

def coverage (j : Fin (m + 1)) : MaximumCoverage (fun i => M.length i j) :=
  Classical.choice (exists_maximumCoverage (fun i => M.length i j) (fun i => M.nonnegative i j))

abbrev AtomIndex := (j : Fin (m + 1)) × Fin (M.coverage j).atomCount

def atomEquiv : M.AtomIndex ≃ Fin (Fintype.card M.AtomIndex) := Fintype.equivFin _

theorem tail_last (i : Fin (m + 1)) :
    (∑ j, if Fin.last m ≤ j then M.length i j else 0) = M.length i (Fin.last m) := by
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro j _ hj
    have hn : ¬Fin.last m ≤ j := by
      intro h
      exact hj (le_antisymm (Fin.le_last j) h)
    simp [hn]
  · simp

theorem terminal_maximum (i : Fin (m + 1)) :
    M.length i (Fin.last m) ≤ M.length (Fin.last m) (Fin.last m) := by
  have h := M.dominated i (Fin.last m)
  simpa only [M.tail_last] using h

def toAtomic : AtomicProfile m (Fintype.card M.AtomIndex) where
  pool a := (M.atomEquiv.symm a).1
  labels a := (M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2
  weight a := (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2
  weight_nonnegative a := ((M.coverage _).weight_positive _).le
  labels_nonempty a := (M.coverage _).labels_nonempty _
  triangular a i hi := by
    have hp := (M.coverage _).labels_positive _ i hi
    by_contra h
    have hz := M.triangular i (M.atomEquiv.symm a).1 (lt_of_not_ge h)
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  terminal a _ hpool := by
    obtain ⟨i, hi⟩ := (M.coverage (M.atomEquiv.symm a).1).labels_nonempty (M.atomEquiv.symm a).2
    apply (M.coverage (M.atomEquiv.symm a).1).labels_upward (M.atomEquiv.symm a).2 i (Fin.last m) ?_ hi
    rw [hpool]
    exact M.terminal_maximum i

theorem coverage_singleton (j i : Fin (m + 1)) :
    (∑ a, if i ∈ (M.coverage j).labels a then (M.coverage j).weight a else 0) =
      M.length i j := by
  have h := (M.coverage j).value_eq {i}
  rw [finiteMaximum_singleton i (fun i => M.length i j) (M.nonnegative i j)] at h
  have hmem (a) : ((M.coverage j).labels a ∩ {i}).Nonempty ↔ i ∈ (M.coverage j).labels a := by
    constructor
    · rintro ⟨x, hx⟩
      have hxi := Finset.mem_singleton.mp (Finset.mem_inter.mp hx).2
      simpa [hxi] using (Finset.mem_inter.mp hx).1
    · intro hi
      exact ⟨i, Finset.mem_inter.mpr ⟨hi, Finset.mem_singleton_self i⟩⟩
  simpa only [hmem] using h.symm

theorem atomic_residual (i t : Fin (m + 1)) :
    M.toAtomic.residual i t = ∑ j, if t ≤ j then M.length i j else 0 := by
  change (∑ a, if t ≤ (M.atomEquiv.symm a).1 ∧
      i ∈ (M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2
    then (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if t ≤ a.1 ∧ i ∈ (M.coverage a.1).labels a.2 then (M.coverage a.1).weight a.2 else 0)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : t ≤ j
  · simpa only [hj, true_and, ite_true] using M.coverage_singleton j i
  · simp [hj]

theorem toAtomic_canonical : M.toAtomic.Canonical := by
  constructor
  · unfold AtomicProfile.designated
    rw [M.atomic_residual]
    simpa using M.initial
  · intro t i
    unfold AtomicProfile.designated
    rw [M.atomic_residual, M.atomic_residual]
    exact M.dominated i t

theorem coverage_total (j : Fin (m + 1)) :
    (∑ a, (M.coverage j).weight a) = finiteMaximum Finset.univ (fun i => M.length i j) := by
  have h := (M.coverage j).value_eq Finset.univ
  simpa [(M.coverage j).labels_nonempty] using h.symm

theorem atomic_baseline (t : Fin (m + 1)) :
    M.toAtomic.baseline t =
      ∑ j, if j < t then finiteMaximum Finset.univ (fun i => M.length i j) else 0 := by
  change (∑ a, if (M.atomEquiv.symm a).1 < t then
    (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if a.1 < t then (M.coverage a.1).weight a.2 else 0), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < t
  · simpa only [hj, ite_true] using M.coverage_total j
  · simp [hj]

theorem atomic_unionValue (t : Fin (m + 1)) (I : Finset (Fin (m + 1))) :
    (∑ a, if t ≤ M.toAtomic.pool a ∧ (M.toAtomic.labels a ∩ I).Nonempty
      then M.toAtomic.weight a else 0) =
      ∑ j, if t ≤ j then finiteMaximum I (fun i => M.length i j) else 0 := by
  change (∑ a, if t ≤ (M.atomEquiv.symm a).1 ∧
      ((M.coverage (M.atomEquiv.symm a).1).labels (M.atomEquiv.symm a).2 ∩ I).Nonempty
    then (M.coverage (M.atomEquiv.symm a).1).weight (M.atomEquiv.symm a).2 else 0) = _
  rw [M.atomEquiv.symm.sum_comp (fun a : M.AtomIndex =>
    if t ≤ a.1 ∧ ((M.coverage a.1).labels a.2 ∩ I).Nonempty then (M.coverage a.1).weight a.2 else 0), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : t ≤ j
  · simpa only [hj, true_and, ite_true] using ((M.coverage j).value_eq I).symm
  · simp [hj]

end TriangularArray

end ConsistentSubmodular
