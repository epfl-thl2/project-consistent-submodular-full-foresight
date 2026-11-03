module

public import ConsistentSubmodular.Deterministic.Certificates.SafePaths

@[expose] public section

/-! Certified checkpoint data. -/

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

/-- A witness contains proofs for the common checkpoint, prescribed endpoints,
every path node and segment, and the combined affine-piece budget. -/
structure CheckpointCertificate (P : AtomicProfile m atomCount) where
  point : Point m
  entry : PolygonalPath m
  exit : PolygonalPath m
  simplex : IsSimplex point
  support : supportCard point ≤ 2
  stages : ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t point
  entry_initial : entry.node 0 = vertex 0
  entry_terminal : entry.node (Fin.last entry.pieces) = point
  exit_initial : exit.node 0 = point
  exit_terminal : exit.node (Fin.last exit.pieces) = vertex (Fin.last m)
  entry_safe : SafePath P 0 ((3 : ℝ) / 4) entry
  exit_safe : SafePath P (Fin.last m)
    ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) exit
  piece_budget : entry.pieces + exit.pieces ≤ (m + 1) + 2

/-- Checkpoint certificates are an equivalent form of `FiniteCheckpointGoal`. -/
theorem finiteCheckpointGoal_iff : FiniteCheckpointGoal ↔
    ∀ m atomCount : ℕ, ∀ P : AtomicProfile m atomCount,
      P.Canonical → Nonempty (CheckpointCertificate P) := by
  constructor
  · intro h m a P hP
    obtain ⟨p, en, ex, hs, hsup, hg, he0, he1, hx0, hx1, hes, hxs, hcount⟩ := h m a P hP
    exact ⟨⟨p, en, ex, hs, hsup, hg, he0, he1, hx0, hx1, hes, hxs, hcount⟩⟩
  · intro h m a P hP
    obtain ⟨c⟩ := h m a P hP
    exact ⟨c.point, c.entry, c.exit, c.simplex, c.support, c.stages,
      c.entry_initial, c.entry_terminal, c.exit_initial, c.exit_terminal,
      c.entry_safe, c.exit_safe, c.piece_budget⟩

end ConsistentSubmodular
