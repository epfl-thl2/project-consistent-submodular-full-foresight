module

public import ConsistentSubmodular.Deterministic.Certificates.SelectorState
public import ConsistentSubmodular.Deterministic.Certificates.SuffConstructor
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackTargets

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- A rollback keeps the original parent's access history and adds one affine
entry piece. A terminal sufficient row supplies the two-piece exit. -/
def checkpoint_of_rollback (hP : P.Canonical) (h : Fin (m + 1)) (H : RelayHistory P h)
    (hk0 : 0 ≤ H.parameter) (hk4 : H.parameter ≤ 4)
    (helig : 0 ≤ P.suffEligibility H.parent H.parameter h)
    (hlater : ∀ t, h ≤ t → (3 : ℝ) / 4 * P.benchmark t ≤
      LowRollback.suffRow P H.parent h t H.parameter) : CheckpointCertificate P := by
  let p := mix (vertex H.parent) (vertex h) (H.parameter / 4)
  let finalEntry := PolygonalPath.segment (vertex H.parent) p
  have hfinalsafe := P.suff_pair_entry hP H.parent h H.advances H.parameter hk0 hk4 helig
  have hjoin : H.parent_access.entry.node (Fin.last H.parent_access.entry.pieces) =
      finalEntry.node 0 := by simpa [finalEntry] using H.parent_access.terminal
  have hexit := P.suff_terminal_exit hP H.parent h (H.parameter / 4)
    (by positivity) (by linarith) (hlater _ (Fin.le_last h))
  let exit := Classical.choose hexit
  have hexit0 := (Classical.choose_spec hexit).1
  have hexit1 := (Classical.choose_spec hexit).2.1
  have hexitsafe := (Classical.choose_spec hexit).2.2.1
  have hexitpieces := (Classical.choose_spec hexit).2.2.2
  change exit.pieces ≤ 2 at hexitpieces
  refine {
    point := p
    entry := PolygonalPath.append H.parent_access.entry finalEntry
    exit := exit
    simplex := (simplex_vertex _).mix (simplex_vertex _) (by positivity) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := ?_
    entry_initial := by rw [PolygonalPath.append_initial, H.parent_access.initial]
    entry_terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    exit_initial := hexit0
    exit_terminal := hexit1
    entry_safe := H.parent_access.safe.append hfinalsafe hjoin
    exit_safe := hexitsafe
    piece_budget := ?_ }
  · intro t
    by_cases hht : h ≤ t
    · exact (hlater t hht).trans (P.value_mix_vertices_sufficient t H.parent h
        (ne_of_lt H.advances) (by positivity) (by linarith)
        (le_min (P.overlap_le_left _ _ _) (P.overlap_le_right _ _ _)))
    · by_cases ha : P.Active t
      · apply P.suff_pair_prefix H.parent h t (ne_of_lt H.advances) H.parameter hk0 hk4
          (le_of_not_ge hht) helig
        by_cases hta : t ≤ H.parent
        · exact P.envelopeSlack_early hP _ _ _ hta
        · exact H.envelope t (lt_of_not_ge hta) ha
      · exact P.inactive_stage_safe t
          ((simplex_vertex _).mix (simplex_vertex _) (by positivity) (by linarith))
          (le_of_not_gt ha)
  · change H.parent_access.entry.pieces + 1 + exit.pieces ≤ (m + 1) + 2
    have hp := H.parent_access.pieces
    have := H.parent.isLt
    omega

end AtomicProfile
end ConsistentSubmodular
