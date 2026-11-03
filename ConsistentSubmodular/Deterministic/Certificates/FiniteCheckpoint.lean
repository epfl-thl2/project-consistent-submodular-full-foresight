module

public import ConsistentSubmodular.Deterministic.Certificates.SelectorLow
public import ConsistentSubmodular.Deterministic.Certificates.SelectorTermination
public import ConsistentSubmodular.Deterministic.Certificates.MiddleRollback
public import ConsistentSubmodular.Deterministic.Certificates.Plateau

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- The complete selector decision, retaining the prescribed branch priority
and advancing strictly whenever a relay is taken. -/
theorem selector_step (hP : P.Canonical) (h : Fin (m + 1)) (S : SelectorState P h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  by_cases hnonpos : P.rawEnvelope h ≤ 0
  · exact Or.inl ⟨P.checkpoint_of_nonpositive hP h S.high.le S.credit S.access hnonpos⟩
  have hpos : 0 < P.rawEnvelope h := lt_of_not_ge hnonpos
  by_cases hlow : P.rawEnvelope h ≤ 1
  · exact Or.inl (P.selector_low_parameter hP h S hpos hlow)
  have hq1 : 1 ≤ P.rawEnvelope h := (lt_of_not_ge hlow).le
  by_cases hlarge : (4 : ℝ) / 3 ≤ P.rawEnvelope h
  · exact P.selector_large_parameter hP h S hlarge
  have hq4 : P.rawEnvelope h < 4 / 3 := lt_of_not_ge hlarge
  by_cases hhigh : (33 : ℝ) / 40 ≤ P.designated h
  · exact P.selector_high_anchor hP h S hq1 (by linarith) hhigh
  by_cases hbase : 3 * (1 - P.designated h) ≤ P.baseline h
  · exact Or.inl (P.checkpoint_of_baseline_stop hP h S.high S.access hbase hq1 (by linarith))
  rcases P.actual_test hP h S.access (P.rawEnvelope h) hq1 (by linarith)
      (P.selector_envelope hP h) with hyes | hno
  · exact Or.inl hyes
  · exact Or.inl (P.middle_parameter_checkpoint hP h S hq1 hq4
      (lt_of_not_ge hhigh) (lt_of_not_ge hbase) hno)

theorem finite_checkpoint_strict (hP : P.Canonical)
    (hstrict : ∀ t : Fin (m + 1), 0 < t → P.designated t < 1) :
    Nonempty (CheckpointCertificate P) := by
  rcases P.root_checkpoint_or_state hP hstrict with hyes | ⟨h, ⟨S⟩⟩
  · exact hyes
  · exact P.checkpoint_of_selector_step (P.selector_step hP) h S

end AtomicProfile

/-- The finite checkpoint theorem, including all stages, both prescribed path
endpoints, every segment and node, and the `d + 2` piece budget. -/
theorem finiteCheckpoint : FiniteCheckpointGoal :=
  finiteCheckpoint_of_strict (fun _ _ P hP hstrict => P.finite_checkpoint_strict hP hstrict)

end ConsistentSubmodular
