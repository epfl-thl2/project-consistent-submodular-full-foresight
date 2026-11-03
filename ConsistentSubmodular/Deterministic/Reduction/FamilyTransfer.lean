module

public import ConsistentSubmodular.Deterministic.Reduction.ProgramAssembly
public import ConsistentSubmodular.Deterministic.Reduction.UniformTransfer

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

/-- Uniform local rounded windows and bridges at level `α - 2/N`, before
concatenating the physical operation lists or scheduling any update. -/
def HasUniformRoundedFamilies (α : ℝ) (N H L : ℕ) : Prop :=
  ∀ n k : ℕ, ∀ f : Objective n, ∀ p : TransferParameters N H k,
    ∃ W : RoundedWindowFamily f p.core (α - 2 * ((1 : ℝ) / N))
      (transferClock f p) (p.core + p.block + H) L,
      Nonempty (RoundedBridgeFamily W)

theorem uniform_programs_of_rounded_families {α : ℝ} {N H L : ℕ}
    (h : HasUniformRoundedFamilies α N H L) :
    HasUniformPrograms α N H (4 * N * (4 * N + 1) * (3 * L + 1)) := by
  intro n k f p
  obtain ⟨W, ⟨T⟩⟩ := h n k f p
  apply W.assemble T (by omega)
  have hh := p.list_fits (3 * L + 1)
  rwa [p.candidates_eq] at hh

end ConsistentSubmodular
