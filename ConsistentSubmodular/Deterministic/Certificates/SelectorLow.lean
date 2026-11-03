module

public import ConsistentSubmodular.Deterministic.Certificates.LowRollback
public import ConsistentSubmodular.Deterministic.Certificates.SelectorRelays

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem selector_low_parameter (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq0 : 0 < P.rawEnvelope h) (hq1 : P.rawEnvelope h ≤ 1) :
    Nonempty (CheckpointCertificate P) := by
  classical
  rcases P.low_actual_test hP h S.high.le S.credit S.access (P.rawEnvelope h)
      hq0 hq1 (P.selector_envelope hP h) with hyes | hno
  · exact hyes
  · obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hq0
    have hhs : h < s := (Finset.mem_filter.mp hs).2.1
    have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
    have hanchor : P.designated h < 1281 / 1600 := by
      by_contra hn
      have he := P.threshold_profile_eligible hP h s hhs.le (le_of_not_gt hn)
        S.credit (P.rawEnvelope h) hq0 hq1 hd heq
      linarith [hno s hhs ha]
    have hparent : 4 / 3 ≤ S.history.parameter := by
      by_contra hn
      have hh := S.history.child_threshold_of_small_parameter hP (lt_of_not_ge hn)
      linarith
    exact LowRollback.low_parameter_checkpoint P hP h S hparent hanchor hq0 hq1 hno

end AtomicProfile
end ConsistentSubmodular
