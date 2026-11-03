module

public import ConsistentSubmodular.Deterministic.Basic.Paths
public import ConsistentSubmodular.Deterministic.Certificates.AtomicFacts

@[expose] public section

/-! Safety of polygonal paths for atomic profiles: constant paths, segments,
concatenation, and reversal. -/

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

theorem safePath_constant_iff (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (level : ℝ) (p : Point m) :
    SafePath P t level (PolygonalPath.constant p) ↔ IsSimplex p ∧ level ≤ P.value t p := by
  constructor
  · intro h
    exact h.1 0
  · intro h
    constructor
    · intro _
      exact h
    · intro j
      exact Fin.elim0 j

theorem safePath_segment (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (level : ℝ) (p q : Point m)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → IsSimplex (mix p q x) ∧
      level ≤ P.value t (mix p q x)) :
    SafePath P t level (PolygonalPath.segment p q) := by
  constructor
  · intro j
    fin_cases j
    · simpa using h 0 le_rfl zero_le_one
    · simpa [PolygonalPath.segment] using h 1 zero_le_one le_rfl
  · intro j x hx hx'
    fin_cases j
    simpa [PolygonalPath.segment] using h x hx hx'

theorem SafePath.append {P : AtomicProfile m atomCount} {t : Fin (m + 1)}
    {level : ℝ} {γ δ : PolygonalPath m} (hγ : SafePath P t level γ)
    (hδ : SafePath P t level δ) (hjoin : γ.node (Fin.last γ.pieces) = δ.node 0) :
    SafePath P t level (PolygonalPath.append γ δ) := by
  constructor
  · intro i
    by_cases hi : i.val ≤ γ.pieces
    · rw [PolygonalPath.append_node_left γ δ i hi]
      exact hγ.1 _
    · rw [PolygonalPath.append_node_right γ δ hjoin i (by omega)]
      exact hδ.1 _
  · intro j x hx hx'
    by_cases hj : j.val < γ.pieces
    · rw [PolygonalPath.append_node_left γ δ j.castSucc (by simpa using Nat.le_of_lt hj),
        PolygonalPath.append_node_left γ δ j.succ (by simpa using hj)]
      exact hγ.2 ⟨j.val, hj⟩ x hx hx'
    · have hj' : γ.pieces ≤ j.val := Nat.le_of_not_gt hj
      rw [PolygonalPath.append_node_right γ δ hjoin j.castSucc (by simpa using hj'),
        PolygonalPath.append_node_right γ δ hjoin j.succ (by simp only [Fin.val_succ]; omega)]
      have hbound : j.val - γ.pieces < δ.pieces := by
        have := j.isLt
        simp only [PolygonalPath.append_pieces] at this
        omega
      have hend : (⟨j.succ.val - γ.pieces, by
          simp only [Fin.val_succ]
          omega⟩ : Fin (δ.pieces + 1)) =
          (⟨j.val - γ.pieces, hbound⟩ : Fin δ.pieces).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hend]
      exact hδ.2 ⟨j.val - γ.pieces, hbound⟩ x hx hx'

theorem SafePath.reverse {P : AtomicProfile m atomCount} {t : Fin (m + 1)}
    {level : ℝ} {γ : PolygonalPath m} (hγ : SafePath P t level γ) :
    SafePath P t level γ.reverse := by
  constructor
  · intro j
    exact hγ.1 j.rev
  · intro j x hx hx'
    change IsSimplex (mix (γ.node j.castSucc.rev) (γ.node j.succ.rev) x) ∧
      level ≤ P.value t (mix (γ.node j.castSucc.rev) (γ.node j.succ.rev) x)
    rw [Fin.rev_castSucc, Fin.rev_succ, mix_swap]
    exact hγ.2 j.rev (1 - x) (by linarith) (by linarith)

end ConsistentSubmodular
