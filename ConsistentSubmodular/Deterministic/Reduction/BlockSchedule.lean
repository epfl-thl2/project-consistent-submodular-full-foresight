module

public import ConsistentSubmodular.Deterministic.Reduction.OperationPath
public import ConsistentSubmodular.Deterministic.Reduction.ProtectedClock

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

/-- Per-block schedules include their common boundary state. -/
structure BlockSchedule (n b R : ℕ) where
  node : ℕ → ℕ → Finset (Fin n)
  joins : ∀ i, node i b = node (i + 1) 0
  step : ∀ i j, j < b → recourse (node i (j + 1)) (node i j) ≤ R

namespace BlockSchedule

variable {n b R : ℕ} (S : BlockSchedule n b R)

def trajectory (t : ℕ) : Finset (Fin n) := S.node (t / b) (t % b)

@[simp] theorem trajectory_zero : S.trajectory 0 = S.node 0 0 := by simp [trajectory]

theorem trajectory_recourse (hb : 0 < b) (t : ℕ) :
    recourse (S.trajectory (t + 1)) (S.trajectory t) ≤ R := by
  have hr := Nat.mod_lt t hb
  have hd0 := Nat.mod_add_div t b
  have hd1 := Nat.mod_add_div (t + 1) b
  by_cases hm : (t + 1) % b = 0
  · have hq := Nat.succ_div_of_mod_eq_zero hm
    have hlast : t % b + 1 = b := by rw [hm, hq] at hd1; nlinarith
    unfold trajectory
    rw [hm, hq, ← S.joins (t / b)]
    simpa only [hlast] using S.step (t / b) (t % b) hr
  · have hq := Nat.succ_div_of_mod_ne_zero hm
    have hnext : (t + 1) % b = t % b + 1 := by rw [hq] at hd1; omega
    unfold trajectory
    rw [hq, hnext]
    exact S.step _ _ hr

end BlockSchedule

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem delayed_batch_recourse (R delay j : ℕ) :
    recourse (P.node (R * (j + 1 - delay))) (P.node (R * (j - delay))) ≤ R := by
  have hmono : R * (j - delay) ≤ R * (j + 1 - delay) :=
    Nat.mul_le_mul_left R (by omega)
  have hdiff : R * (j + 1 - delay) - R * (j - delay) ≤ R := by
    have hm := Nat.mul_le_mul_left R (show j + 1 - delay ≤ (j - delay) + 1 by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  exact (P.recourse_le_difference hmono).trans hdiff

end SetOperationPath

namespace ProtectedClock

variable {n b ell R : ℕ} {F : ℕ → ℝ} {η : ℝ}
variable (C : ProtectedClock F η b ell)

def delay (i : ℕ) : ℕ := C.start i - (i + 1) * b

theorem delay_fit (i : ℕ) : C.delay i + ell ≤ b := by
  have hl := C.lower i
  have hu := C.upper i
  have hh : C.start i + ell ≤ (i + 1) * b + b := by nlinarith
  dsimp [delay]
  omega

def coreBlocks (P : ℕ → SetOperationPath n)
    (hinitial : (P 0).node 0 = ∅)
    (hjoin : ∀ i, (P i).node (P i).length = (P (i + 1)).node 0)
    (hlen : ∀ i, (P i).length ≤ R * ell) : BlockSchedule n b R := by
  let seq : ℕ → ℕ → Finset (Fin n) := fun i j =>
    match i with
    | 0 => ∅
    | i + 1 => (P i).node (R * (j - C.delay i))
  refine { node := seq, joins := ?_, step := ?_ }
  · intro i
    cases i with
    | zero => simpa [seq] using hinitial.symm
    | succ i =>
      have hfit := C.delay_fit i
      have hfinish : (P i).length ≤ R * (b - C.delay i) :=
        (hlen i).trans (Nat.mul_le_mul_left R (by omega))
      simpa [seq, (P i).stationary _ hfinish] using hjoin i
  · intro i j _
    cases i with
    | zero => simp [seq, recourse]
    | succ i => exact (P i).delayed_batch_recourse R (C.delay i) j

theorem coreBlocks_initial (P : ℕ → SetOperationPath n) (hinitial hjoin hlen) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory 0 = ∅ := by
  simp [BlockSchedule.trajectory, coreBlocks]

theorem coreBlocks_recourse (hb : 0 < b) (P : ℕ → SetOperationPath n)
    (hinitial hjoin hlen) (t : ℕ) :
    recourse ((C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory (t + 1))
      ((C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t) ≤ R :=
  BlockSchedule.trajectory_recourse _ hb t

theorem coreBlocks_before_first (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (t : ℕ) (ht : t / b = 0) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t = ∅ := by
  simp [BlockSchedule.trajectory, coreBlocks, ht]

theorem coreBlocks_in_block (P : ℕ → SetOperationPath n) (hinitial hjoin hlen)
    (i t : ℕ) (ht : t / b = i + 1) :
    (C.coreBlocks (R := R) P hinitial hjoin hlen).trajectory t =
      (P i).node (R * (t - C.start i)) := by
  have htval := Nat.mod_add_div t b
  rw [ht] at htval
  have hl := C.lower i
  have heq : t % b - C.delay i = t - C.start i := by
    dsimp [delay]
    have hh : t % b + (i + 1) * b = t := by nlinarith
    omega
  simp [BlockSchedule.trajectory, coreBlocks, ht, heq]

end ProtectedClock
end ConsistentSubmodular
