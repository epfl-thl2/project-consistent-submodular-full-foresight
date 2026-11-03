module

public import ConsistentSubmodular.Deterministic.Reduction.WindowOperationAssembly
public import ConsistentSubmodular.Deterministic.Reduction.WindowSampling

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace FractionalWindow

variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

/-- Every bounded-complexity fractional window has an endpoint-preserving
physical realization, including zero scale and zero-piece paths. -/
theorem exists_rounded (hN : 200 ≤ N) (hS : 0 < S) (hκ : windowHeavyBound N S ≤ κ) :
    Nonempty (RoundedWindow W (windowHeavyBound N S) (windowLengthBound S)) := by
  by_cases hV : f.bufferedOptimum old ∅ κ = 0
  · exact W.rounded_of_zero_scale hV _ _ (by unfold windowLengthBound; omega)
  · have hVpos : 0 < f.bufferedOptimum old ∅ κ :=
      lt_of_le_of_ne (f.bufferedOptimum_nonnegative _ _ _) (Ne.symm hV)
    obtain ⟨Smp⟩ := W.exists_windowSamples hN hS hκ hVpos
    exact Smp.toRounded hκ

end FractionalWindow
end ConsistentSubmodular
