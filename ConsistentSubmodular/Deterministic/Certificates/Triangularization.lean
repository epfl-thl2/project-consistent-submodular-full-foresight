module

public import ConsistentSubmodular.Deterministic.Certificates.ArrayCompletion

@[expose] public section

/-! Triangularizing least compatible completion with all stage labels fixed. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

theorem fin_tail_step {m : ℕ} (a : Fin (m + 1) → ℝ) (t : Fin m) :
    (∑ j, if t.castSucc ≤ j then a j else 0) =
      a t.castSucc + ∑ j, if t.succ ≤ j then a j else 0 := by
  have hpoint (j : Fin (m + 1)) :
      (if t.castSucc ≤ j then a j else 0) =
        (if j = t.castSucc then a j else 0) + (if t.succ ≤ j then a j else 0) := by
    by_cases heq : j = t.castSucc
    · subst j
      simp
    · have hiff : t.castSucc ≤ j ↔ t.succ ≤ j := by
        have hne : j.val ≠ t.val := by intro h; exact heq (Fin.ext h)
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        omega
      simp [heq, hiff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem fin_before_step {m : ℕ} (a : Fin (m + 1) → ℝ) (t : Fin m) :
    (∑ j, if j < t.succ then a j else 0) =
      (∑ j, if j < t.castSucc then a j else 0) + a t.castSucc := by
  have hpoint (j : Fin (m + 1)) :
      (if j < t.succ then a j else 0) =
        (if j < t.castSucc then a j else 0) + (if j = t.castSucc then a j else 0) := by
    by_cases heq : j = t.castSucc
    · subst j
      simp
    · have hiff : j < t.succ ↔ j < t.castSucc := by
        have hne : j.val ≠ t.val := by intro h; exact heq (Fin.ext h)
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega
      simp [heq, hiff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

theorem fin_tail_last {m : ℕ} (a : Fin (m + 1) → ℝ) :
    (∑ j, if Fin.last m ≤ j then a j else 0) = a (Fin.last m) := by
  rw [Finset.sum_eq_single (Fin.last m)]
  · simp
  · intro j _ hj
    have hn : ¬Fin.last m ≤ j := fun h => hj (le_antisymm (Fin.le_last j) h)
    simp [hn]
  · simp

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

def rawLength (i j : Fin (m + 1)) : ℝ :=
  if j = Fin.last m then P.residual m i else P.loss j.val i

def triangularLength (i j : Fin (m + 1)) : ℝ :=
  if i ≤ j then P.rawLength i j else 0

theorem rawLength_nonnegative (i j : Fin (m + 1)) : 0 ≤ P.rawLength i j := by
  unfold rawLength
  split_ifs
  · exact P.residualOn_nonnegative m {i}
  · exact P.loss_nonnegative j.val i

theorem triangularLength_nonnegative (i j : Fin (m + 1)) : 0 ≤ P.triangularLength i j := by
  unfold triangularLength
  split_ifs
  · exact P.rawLength_nonnegative i j
  · rfl

theorem triangularLength_le_raw (i j : Fin (m + 1)) :
    P.triangularLength i j ≤ P.rawLength i j := by
  unfold triangularLength
  split_ifs
  · rfl
  · exact P.rawLength_nonnegative i j

theorem rawLength_tail (i t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.rawLength i j else 0) = P.residual t.val i := by
  induction t using Fin.reverseInduction with
  | last => simp [rawLength]
  | cast t ih =>
    rw [fin_tail_step, ih]
    simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, Fin.val_succ, loss]
    ring

theorem triangularLength_designated (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.triangularLength t j else 0) = P.residual t.val t := by
  calc
    _ = ∑ j, if t ≤ j then P.rawLength t j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : t ≤ j <;> simp [triangularLength, hj]
    _ = _ := P.rawLength_tail t t

theorem triangularLength_tail_le (i t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.triangularLength i j else 0) ≤ P.residual t.val i := by
  rw [← P.rawLength_tail i t]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact P.triangularLength_le_raw i j
  · rfl

/-- Labels remain their prescribed stage labels, even when physical cores
coincide. Only already-buffered coverage is removed from each label. -/
def toTriangularArray (hinit : P.residual 0 0 = 1)
    (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t) :
    TriangularArray m where
  length := P.triangularLength
  nonnegative := P.triangularLength_nonnegative
  triangular i j hij := by simp [triangularLength, not_le.mpr hij]
  initial := by
    have h := P.triangularLength_designated 0
    simpa [hinit] using h
  dominated i t := by
    rw [P.triangularLength_designated]
    exact (P.triangularLength_tail_le i t).trans (hopt t i)

theorem triangular_pool_le_raw (I : Finset (Fin (m + 1))) (j : Fin (m + 1)) :
    finiteMaximum I (fun i => P.triangularLength i j) ≤
      finiteMaximum I (fun i => P.rawLength i j) := by
  apply finiteMaximum_le (finiteMaximum_nonnegative (fun i _ => P.rawLength_nonnegative i j))
  exact fun i hi => (P.triangularLength_le_raw i j).trans
    (le_finiteMaximum (g := fun i => P.rawLength i j) hi)

theorem raw_union_tail_le (I : Finset (Fin (m + 1))) (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then finiteMaximum I (fun i => P.rawLength i j) else 0) ≤
      P.residualOn t.val I := by
  induction t using Fin.reverseInduction with
  | last =>
    rw [fin_tail_last]
    simpa only [rawLength, ite_true, Fin.val_last] using P.terminalValue_le_residual m I
  | cast t ih =>
    rw [fin_tail_step]
    have hpool := P.poolValue_le_residual_drop t.val I
    have hraw : finiteMaximum I (fun i => P.rawLength i t.castSucc) = P.poolValue t.val I := by
      simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, poolValue]
    rw [hraw]
    simp only [Fin.val_succ, Fin.val_castSucc] at *
    linarith

theorem triangular_union_tail_le (I : Finset (Fin (m + 1))) (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then finiteMaximum I (fun i => P.triangularLength i j) else 0) ≤
      P.residualOn t.val I := by
  apply le_trans _ (P.raw_union_tail_le I t)
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact P.triangular_pool_le_raw I j
  · rfl

theorem triangular_baseline_le (t : Fin (m + 1)) :
    (∑ j, if j < t then finiteMaximum Finset.univ (fun i => P.triangularLength i j) else 0) ≤
      P.baseline t.val := by
  induction t using Fin.induction with
  | zero => simpa [baseline] using (P.objective 0).nonnegative ∅
  | succ t ih =>
    rw [fin_before_step]
    have hraw : finiteMaximum Finset.univ (fun i => P.rawLength i t.castSucc) =
        P.poolValue t.val Finset.univ := by
      simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, poolValue]
    have htri := P.triangular_pool_le_raw Finset.univ t.castSucc
    rw [hraw] at htri
    have hpay := P.pool_total_le_baseline_increment t.val
    simp only [Fin.val_castSucc, Fin.val_succ] at *
    linarith

end CompatibleProfile

end ConsistentSubmodular
