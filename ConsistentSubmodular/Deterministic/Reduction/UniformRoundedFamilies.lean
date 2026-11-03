module

public import ConsistentSubmodular.Deterministic.Reduction.ClockRounded
public import ConsistentSubmodular.Deterministic.Reduction.RoundedWindowExistence
public import ConsistentSubmodular.Deterministic.Reduction.BridgeRounding
public import ConsistentSubmodular.Deterministic.Reduction.FamilyTransfer

@[expose] public section

/-! The concrete uniform local families. Their two constants depend only on
integer accuracy and on the segment budget of compressed windows, before the
level and all stream, budget, and objective parameters. -/

noncomputable section
namespace ConsistentSubmodular

/-- Cardinality reserve for the forced elements of windows and bridges. -/
def familyHeavy (N S : ℕ) : ℕ := windowHeavyBound N S + bridgeHeavy N

/-- Operation coefficient for windows and bridges. -/
def familyLength (S : ℕ) : ℕ := windowLengthBound S + 10

/-- Endpoint-preserving local families supply the rounded windows and bridges of
the schedule at the level of the certificates. The constants are independent of
the instance and of the level. -/
theorem uniformRoundedFamilies (O : CertificateFamily) (N : ℕ) (hN : 200 ≤ N) :
    HasUniformRoundedFamilies O.level N (familyHeavy N (O.budget (3 * N + 1)))
      (familyLength (O.budget (3 * N + 1))) := by
  intro n k f p
  let H := familyHeavy N (O.budget (3 * N + 1))
  let L := familyLength (O.budget (3 * N + 1))
  let C := transferClock f p
  have hN0 : 0 < N := by omega
  have hS : 0 < O.budget (3 * N + 1) := O.budget_pos _
  have hHW : windowHeavyBound N (O.budget (3 * N + 1)) ≤ p.core := by
    have hh := p.core_large
    dsimp only [familyHeavy] at hh
    omega
  let R := fun i => Classical.choice ((C.fractionalWindows f p.core O N hN0 i).exists_rounded hN hS hHW)
  apply C.rounded_families f p.core O N hN (windowHeavyBound N (O.budget (3 * N + 1)))
    (windowLengthBound (O.budget (3 * N + 1))) (bridgeHeavy N) 10 (p.core + p.block + H) L R
  · have hs := p.rounding_slack
    have hh : (windowHeavyBound N (O.budget (3 * N + 1)) : ℝ) ≤ H := by
      exact_mod_cast (show windowHeavyBound N (O.budget (3 * N + 1)) ≤ H by dsimp [H, familyHeavy]; omega)
    push_cast
    linarith
  · have hs := p.rounding_slack
    have hh : (bridgeHeavy N : ℝ) ≤ H := by
      exact_mod_cast (show bridgeHeavy N ≤ H by dsimp [H, familyHeavy]; omega)
    push_cast
    linarith
  · dsimp [L, familyLength]
    omega
  · dsimp [L, familyLength]
    omega
  · intro i
    have hterminal := C.windowTerminal_spec f p.core i
    have hinitial := C.windowInitial_spec f p.core (i + 1)
    obtain ⟨hA, hB, hAv, hBv⟩ := C.window_bridge_endpoints f p.core i
    obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_rounded_bridge (C.windowTerminal f p.core i)
      (C.windowInitial f p.core (i + 1)) (C.windowBuffer n i (C.windowDuration i)) N p.core
      (f.prefixOptimum p.core (C.start (i + 1))) hN0 (f.prefixOptimum_nonnegative _ _)
      hterminal.2.1 hinitial.2.1 hAv hBv hA hB
    refine ⟨P, h0, h1, hlen, fun j => ⟨(hnode j).1, (hnode j).2.1, ?_⟩⟩
    have hV := f.prefixOptimum_nonnegative p.core (C.start (i + 1))
    exact (mul_le_mul_of_nonneg_right (by linarith [O.level_le]) hV).trans (hnode j).2.2

end ConsistentSubmodular
