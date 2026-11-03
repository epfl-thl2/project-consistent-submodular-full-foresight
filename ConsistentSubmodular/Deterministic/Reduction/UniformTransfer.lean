module

public import ConsistentSubmodular.Deterministic.Reduction.StreamingComparison

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

def transferClock {N H k n : ℕ} (f : Objective n) (p : TransferParameters N H k) :
    ProtectedClock (f.prefixOptimum k) ((1 : ℝ) / N) p.block p.interval :=
  protectedClock (f.prefixOptimum k) (f.prefixOptimum_monotone k)
    (f.prefixOptimum_nonnegative k) p.block p.candidates p.interval
    p.candidates_pos p.fit ((1 : ℝ) / N) (by positivity) p.growth

/-- Rounded local programs at level `α - 2/N`. Their constants are chosen before
every instance parameter. -/
def HasUniformPrograms (α : ℝ) (N H R : ℕ) : Prop :=
  ∀ n k : ℕ, ∀ f : Objective n, ∀ p : TransferParameters N H k,
    Nonempty (ProtectedPrograms f p.core (α - 2 * ((1 : ℝ) / N))
      (transferClock f p) R (p.core + p.block + H))

/-- A level at most the slack needs no recourse: the empty trajectory meets it. -/
theorem consistentGuarantee_of_le_slack {α ε : ℝ} (h : α ≤ ε) (R : ℕ) :
    ConsistentGuarantee α ε R := by
  intro n k f
  refine ⟨fun _ => ∅, ⟨rfl, fun _ => ⟨Finset.empty_subset _, by simp⟩,
    fun _ => by simp [recourse]⟩, ?_⟩
  intro t A _ _
  have hA := f.nonnegative A
  have h0 := f.nonnegative ∅
  nlinarith

/-- Complete uniform transfer from the finite family of rounded local
programs. Small budgets use exact optimization. A level at most `ε` needs no
programs: the empty trajectory already meets it. -/
theorem guarantee_of_uniform_programs {α ε : ℝ} {N H R : ℕ} (hN : 200 ≤ N)
    (hα : α ≤ 3 / 4) (hNε : 20 * ((1 : ℝ) / N) < ε)
    (hprograms : HasUniformPrograms α N H R) :
    ConsistentGuarantee α ε (2 * transferThreshold N H + R + 2) := by
  by_cases hαε : α ≤ ε
  · exact consistentGuarantee_of_le_slack hαε _
  intro n k f
  have hη0 : 0 ≤ (1 : ℝ) / N := by positivity
  have hγ : 0 ≤ α - 14 * ((1 : ℝ) / N) := by linarith
  let K := transferThreshold N H
  by_cases hk : k ≤ K
  · obtain ⟨S, hS, hval⟩ := small_budget_trajectory K k hk f
      (show α - ε ≤ 1 by linarith)
    refine ⟨S, ⟨hS.1, hS.2.1, ?_⟩, hval⟩
    intro t
    exact (hS.2.2 t).trans (by omega)
  · have hklarge : transferThreshold N H ≤ k := by dsimp [K] at hk; omega
    let p := transferParameters N H k hN hklarge
    obtain ⟨P⟩ := hprograms n k f p
    have hkp : 0 < k := by omega
    obtain ⟨hfeas, hval⟩ := P.trajectory_spec p hkp hα hγ
    refine ⟨(fun t => P.selected t.val), ⟨hfeas.1, hfeas.2.1, ?_⟩, ?_⟩
    · intro t
      exact (hfeas.2.2 t).trans (by omega)
    · intro t A hA hAk
      have hcoef : α - ε ≤ α - 14 * ((1 : ℝ) / N) := by linarith
      exact (mul_le_mul_of_nonneg_right hcoef (f.nonnegative A)).trans (hval t A hA hAk)

end ConsistentSubmodular
