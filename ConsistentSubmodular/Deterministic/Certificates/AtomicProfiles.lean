module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# Atomic profiles

The finite coverage model of the proof of Theorem 7: atomic profiles, their
values at the points of the simplex, safe paths, and the finite checkpoint
statement `FiniteCheckpointGoal` (Definition 2.1 and Theorem 2.2 of
`docs/three_quarter_certificate.pdf`). `WindowCertificates` derives Theorem 7
from it.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

def supportCard {m : ℕ} (p : Point m) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => p i ≠ 0)).card

/-- Finite atoms; positive terminal atoms contain the prescribed terminal label. -/
structure AtomicProfile (m atomCount : ℕ) where
  pool : Fin atomCount → Fin (m + 1)
  labels : Fin atomCount → Finset (Fin (m + 1))
  weight : Fin atomCount → ℝ
  weight_nonnegative : ∀ a, 0 ≤ weight a
  labels_nonempty : ∀ a, (labels a).Nonempty
  triangular : ∀ a i, i ∈ labels a → i ≤ pool a
  terminal : ∀ a,
    0 < weight a → pool a = Fin.last m → Fin.last m ∈ labels a

namespace AtomicProfile

variable {m atomCount : ℕ}

def baseline (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  ∑ a, if P.pool a < t then P.weight a else 0

def residual (P : AtomicProfile m atomCount)
    (i t : Fin (m + 1)) : ℝ :=
  ∑ a, if t ≤ P.pool a ∧ i ∈ P.labels a then P.weight a else 0

def designated (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  P.residual t t

def benchmark (P : AtomicProfile m atomCount) (t : Fin (m + 1)) : ℝ :=
  P.baseline t + P.designated t

def value (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (p : Point m) : ℝ :=
  P.baseline t + ∑ a,
    if t ≤ P.pool a then
      P.weight a * (1 - ∏ i ∈ P.labels a, (1 - p i))
    else 0

def Canonical (P : AtomicProfile m atomCount) : Prop :=
  P.designated 0 = 1 ∧
  ∀ (t i : Fin (m + 1)), P.residual i t ≤ P.designated t

end AtomicProfile

/-- Nodes are checked explicitly, so a zero-piece path is not vacuously safe. -/
def SafePath {m atomCount : ℕ} (P : AtomicProfile m atomCount)
    (t : Fin (m + 1)) (level : ℝ) (γ : PolygonalPath m) : Prop :=
  (∀ j, IsSimplex (γ.node j) ∧ level ≤ P.value t (γ.node j)) ∧
  ∀ (j : Fin γ.pieces) (x : ℝ), 0 ≤ x → x ≤ 1 →
    IsSimplex (mix (γ.node j.castSucc) (γ.node j.succ) x) ∧
    level ≤ P.value t (mix (γ.node j.castSucc) (γ.node j.succ) x)

/-- The finite checkpoint statement, including endpoint safety, support, and
piece budget. -/
def FiniteCheckpointGoal : Prop :=
  ∀ m atomCount : ℕ, ∀ P : AtomicProfile m atomCount,
    P.Canonical →
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      SafePath P 0 ((3 : ℝ) / 4) entry ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2

end ConsistentSubmodular
