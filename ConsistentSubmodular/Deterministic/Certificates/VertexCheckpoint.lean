module

public import ConsistentSubmodular.Deterministic.Certificates.Access
public import ConsistentSubmodular.Deterministic.Certificates.ActualCheckpoint

@[expose] public section

/-! The complete nonpositive-envelope branch of the selector. -/

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem vertex_stages_of_nonpositive (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hraw : P.rawEnvelope h ≤ 0) :
    ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t (vertex h) := by
  classical
  have hzero : P.rawEnvelope h = 0 := le_antisymm hraw (P.rawEnvelope_nonnegative h)
  intro t
  by_cases ht : P.Active t
  · rw [P.value_vertex]
    by_cases hth : t ≤ h
    · rw [P.residual_persistence h t hth]
      have hb := P.baseline_nonnegative t
      have hg := P.designated_le_one hP t
      unfold benchmark
      linarith
    · have henv := P.rawEnvelope_valid hP h t
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hth, ht⟩)
      rw [hzero] at henv
      unfold envelopeSlack benchmark at *
      nlinarith
  · exact P.inactive_stage_safe t (simplex_vertex h) (le_of_not_gt ht)

def checkpoint_of_nonpositive (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hcredit : P.StrongCredit h)
    (access : AccessCertificate P h) (hraw : P.rawEnvelope h ≤ 0) :
    CheckpointCertificate P := by
  classical
  have hstages := P.vertex_stages_of_nonpositive hP h hA hraw
  have hzero : P.rawEnvelope h = 0 := le_antisymm hraw (P.rawEnvelope_nonnegative h)
  have hexit : ∃ γ : PolygonalPath m,
      γ.node 0 = vertex h ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
    by_cases hh : h = Fin.last m
    · refine ⟨PolygonalPath.constant (vertex h), rfl, ?_, ?_, by simp⟩
      · simp [hh]
      · exact (safePath_constant_iff _ _ _ _).2 ⟨simplex_vertex h, hstages _⟩
    · by_cases ht : P.Active (Fin.last m)
      · have henv := P.rawEnvelope_valid hP h (Fin.last m)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_le_of_ne (Fin.le_last h) hh, ht⟩)
        rw [hzero] at henv
        have hterm := P.terminal_envelope_inequality h 0 henv
        have hbase := P.strongCredit_baseline hP h hA hcredit
        have hpersist := P.baseline_add_residual_monotone h (Fin.le_last h)
        change P.baseline h + P.designated h ≤
          P.baseline (Fin.last m) + P.residual h (Fin.last m) at hpersist
        have hbudget : 3 ≤ P.designated h +
            2 * (P.baseline (Fin.last m) + P.residual h (Fin.last m)) := by
          have hA1 := P.designated_le_one hP h
          linarith
        have he := P.actual_terminal_exit_of_budget hP h (Fin.last m) hh 0
          (by norm_num) (by norm_num) (by simpa using hstages (Fin.last m))
          hbudget (by simpa using hterm)
        simpa using he
      · exact P.inactive_terminal_exit _ (simplex_vertex h) ht
  let exit := Classical.choose hexit
  have he := Classical.choose_spec hexit
  exact {
    point := vertex h
    entry := access.entry
    exit := exit
    simplex := simplex_vertex h
    support := by rw [supportCard_vertex]; norm_num
    stages := hstages
    entry_initial := access.initial
    entry_terminal := access.terminal
    exit_initial := he.1
    exit_terminal := he.2.1
    entry_safe := access.safe
    exit_safe := he.2.2.1
    piece_budget := by
      have hp := access.pieces
      have hepiece : exit.pieces ≤ 2 := he.2.2.2
      have hh := h.isLt
      omega }

end AtomicProfile
end ConsistentSubmodular
