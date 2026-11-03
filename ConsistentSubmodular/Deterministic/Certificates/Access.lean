module

public import ConsistentSubmodular.Deterministic.Certificates.BaselineStop
public import ConsistentSubmodular.Deterministic.Certificates.HighAnchor
public import ConsistentSubmodular.Deterministic.Certificates.Checkpoint

@[expose] public section

/-! Initial accessibility and strong-credit transport along finite relays. -/

noncomputable section
namespace ConsistentSubmodular

variable {m atomCount : ℕ}

structure AccessCertificate (P : AtomicProfile m atomCount) (h : Fin (m + 1)) where
  entry : PolygonalPath m
  initial : entry.node 0 = vertex 0
  terminal : entry.node (Fin.last entry.pieces) = vertex h
  safe : SafePath P 0 ((3 : ℝ) / 4) entry
  pieces : entry.pieces ≤ h.val

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

def StrongCredit (h : Fin (m + 1)) : Prop :=
  (1 : ℝ) / 2 ≤ P.benchmark h - 1 ∨
    1 - P.designated h ≤ (P.benchmark h - 1) * (1 - (P.benchmark h - 1))

def PessimisticSafeEdge (h s : Fin (m + 1)) : Prop :=
  ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 ≤
    P.designated h - (P.designated h - P.designated s) * z -
      P.residual h s * z * (1 - z)

def rootAccess (hP : P.Canonical) : AccessCertificate P 0 where
  entry := PolygonalPath.constant (vertex 0)
  initial := rfl
  terminal := rfl
  safe := by
    apply (safePath_constant_iff _ _ _ _).2
    refine ⟨simplex_vertex 0, ?_⟩
    rw [P.value_designated_vertex, P.benchmark_zero hP]
    norm_num
  pieces := by simp

theorem root_strongCredit (hP : P.Canonical) : P.StrongCredit 0 := by
  right
  rw [P.benchmark_zero hP, hP.1]
  norm_num

theorem pessimisticEdge_safe (h s : Fin (m + 1)) (hhs : h < s)
    (hsafe : P.PessimisticSafeEdge h s) :
    SafePath P 0 ((3 : ℝ) / 4) (PolygonalPath.segment (vertex h) (vertex s)) := by
  apply safePath_segment
  intro z hz hz1
  refine ⟨(simplex_vertex h).mix (simplex_vertex s) hz hz1, ?_⟩
  have hlow := P.value_mix_vertices_lower 0 h s (ne_of_lt hhs) hz hz1
    (P.overlap_le_persistent h s 0)
  rw [P.baseline_zero, P.residual_persistence h 0 (Fin.zero_le _),
    P.residual_persistence s 0 (Fin.zero_le _)] at hlow
  have hs := hsafe z hz hz1
  nlinarith

def extendAccess (h s : Fin (m + 1)) (hhs : h < s)
    (access : AccessCertificate P h) (hsafe : P.PessimisticSafeEdge h s) :
    AccessCertificate P s := by
  let seg := PolygonalPath.segment (vertex h) (vertex s)
  have hjoin : access.entry.node (Fin.last access.entry.pieces) = seg.node 0 := access.terminal
  exact {
    entry := PolygonalPath.append access.entry seg
    initial := by rw [PolygonalPath.append_initial, access.initial]
    terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    safe := access.safe.append (P.pessimisticEdge_safe h s hhs hsafe) hjoin
    pieces := by
      simp only [PolygonalPath.append_pieces]
      change access.entry.pieces + 1 ≤ s.val
      have := access.pieces
      have : h.val < s.val := hhs
      omega }

theorem strongCredit_of_pessimisticEdge (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s) (hsafe : P.PessimisticSafeEdge h s) :
    P.StrongCredit s := by
  have hpersist := P.persistence_credit h s hhs
  have hcanon := P.one_le_benchmark hP h
  unfold benchmark at hcanon
  exact safe_relay_strong_credit (P.designated h) (P.designated s) (P.residual h s)
    (P.benchmark s - 1) (P.designated_le_one hP h) (P.designated_antitone hP hhs)
    (P.residual_nonnegative h s) (hP.2 s h) (by linarith) hsafe

theorem strongCredit_baseline (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hc : P.StrongCredit h) :
    2 * (1 - P.designated h) ≤ P.baseline h :=
  strong_credit_baseline (P.designated h) (P.baseline h)
    (P.designated_le_one hP h) hc hA

theorem attaining_equation (h s : Fin (m + 1)) (q : ℝ)
    (hd : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q) :
    (3 - q) * (P.designated s - P.residual h s) =
      q * (P.designated h - P.designated s) +
      ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) +
      3 * (1 - P.designated h) := by
  have hh := (div_eq_iff (ne_of_gt hd)).mp heq
  unfold rawNumerator at hh
  nlinarith only [hh]

theorem high_parameter_profile_relay (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h < s)
    (hA : (3 : ℝ) / 4 < P.designated h) (hcredit : P.StrongCredit h)
    (q : ℝ) (hq : (3 : ℝ) / 2 ≤ q)
    (hden : 0 < P.designated h - P.residual h s) (heq : P.rawRatio h s = q)
    (hfail : q * (P.benchmark s - P.designated h) <
      2 * P.designated h * q - 3 * (4 * P.designated h - 3)) :
    (∀ z : ℝ, (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z)) ∧
      (3 : ℝ) / 4 < P.designated s ∧ P.StrongCredit s := by
  have hA1 := P.designated_le_one hP h
  have hδ := sub_nonneg.mpr (P.designated_antitone hP hhs.le)
  have hw := sub_nonneg.mpr (hP.2 s h)
  have hr := P.residual_nonnegative h s
  have hp := P.one_le_benchmark hP h
  have hper := P.persistence_credit h s hhs.le
  have hatt := P.attaining_equation h s q hden heq
  have hscalar := high_parameter_strict_relay (1 - P.designated h)
    (P.benchmark h - 1) (P.designated h - P.designated s)
    (P.designated s - P.residual h s)
    ((P.benchmark s - P.designated h) - (P.designated s - P.residual h s)) q
    (by linarith) (by linarith) (by linarith) hcredit hδ hw (by linarith)
    (by linarith) (by unfold benchmark at *; linarith) hq
    (by nlinarith only [hatt]) (by nlinarith only [hfail])
  have hstrict : ∀ z : ℝ, (3 : ℝ) / 4 < P.designated h -
      (P.designated h - P.designated s) * z - P.residual h s * z * (1 - z) := by
    intro z
    have := hscalar z
    nlinarith only [this]
  refine ⟨hstrict, ?_, P.strongCredit_of_pessimisticEdge hP h s hhs.le
    (fun z _ _ => (hstrict z).le)⟩
  have := hstrict 1
  norm_num at this
  linarith

end AtomicProfile
end ConsistentSubmodular
