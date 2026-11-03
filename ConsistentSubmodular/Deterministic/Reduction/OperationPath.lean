module

public import ConsistentSubmodular.Deterministic.Reduction.SchedulingBasics

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

/-- A finite list of physical insertions and deletions, extended constantly
after its endpoint. Stuttering steps are permitted. -/
structure SetOperationPath (n : ℕ) where
  length : ℕ
  node : ℕ → Finset (Fin n)
  stationary : ∀ i, length ≤ i → node i = node length
  step : ∀ i, recourse (node (i + 1)) (node i) ≤ 1

namespace SetOperationPath

variable {n : ℕ} (P : SetOperationPath n)

theorem interval_recourse (a d : ℕ) : recourse (P.node (a + d)) (P.node a) ≤ d := by
  induction d with
  | zero => simp [recourse]
  | succ d ih =>
    have ht := recourse_triangle (P.node (a + (d + 1))) (P.node (a + d)) (P.node a)
    have hs := P.step (a + d)
    rw [Nat.add_assoc] at hs
    omega

theorem recourse_le_difference {a b : ℕ} (hab : a ≤ b) :
    recourse (P.node b) (P.node a) ≤ b - a := by
  simpa [Nat.add_sub_of_le hab] using P.interval_recourse a (b - a)

def constant (A : Finset (Fin n)) : SetOperationPath n where
  length := 0
  node := fun _ => A
  stationary := by intros; rfl
  step := by intro; simp [recourse]

def append (Q : SetOperationPath n) (hjoin : P.node P.length = Q.node 0) :
    SetOperationPath n := by
  let seq := fun i => if i ≤ P.length then P.node i else Q.node (i - P.length)
  have hbefore (i : ℕ) (hi : i ≤ P.length) : seq i = P.node i := by simp [seq, hi]
  have hafter (i : ℕ) (hi : P.length ≤ i) : seq i = Q.node (i - P.length) := by
    by_cases he : i = P.length
    · subst i
      simp [seq, hjoin]
    · simp [seq, show ¬i ≤ P.length by omega]
  refine {
    length := P.length + Q.length
    node := seq
    stationary := ?_
    step := ?_ }
  · intro i hi
    rw [hafter i (by omega), hafter (P.length + Q.length) (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact Q.stationary _ (by omega)
  · intro i
    by_cases hi : i < P.length
    · rw [hbefore (i + 1) (by omega), hbefore i (by omega)]
      exact P.step i
    · rw [hafter (i + 1) (by omega), hafter i (by omega)]
      rw [show i + 1 - P.length = (i - P.length) + 1 by omega]
      exact Q.step _

@[simp] theorem append_length (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).length = P.length + Q.length := rfl

@[simp] theorem append_initial (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).node 0 = P.node 0 := by simp [append]

@[simp] theorem append_terminal (Q : SetOperationPath n) (hjoin) :
    (P.append Q hjoin).node (P.length + Q.length) = Q.node Q.length := by
  by_cases hQ : Q.length = 0
  · simp [append, hQ, hjoin]
  · simp [append, show ¬P.length + Q.length ≤ P.length by omega]

theorem append_property (Q : SetOperationPath n) (hjoin)
    (good : Finset (Fin n) → Prop) (hP : ∀ i, good (P.node i))
    (hQ : ∀ i, good (Q.node i)) : ∀ i, good ((P.append Q hjoin).node i) := by
  intro i
  change good (if i ≤ P.length then P.node i else Q.node (i - P.length))
  split
  · exact hP i
  · exact hQ _

end SetOperationPath
end ConsistentSubmodular
