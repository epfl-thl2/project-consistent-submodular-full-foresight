module

public import ConsistentSubmodular.Deterministic.Certificates.RootInitialization
public import ConsistentSubmodular.Deterministic.Certificates.SelectorRelays

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

/-- Any complete local decision rule terminates because every relay strictly
increases its finite carrier index. -/
theorem checkpoint_of_selector_step
    (step : ∀ h, SelectorState P h → Nonempty (CheckpointCertificate P) ∨
      ∃ s, h < s ∧ Nonempty (SelectorState P s))
    (h : Fin (m + 1)) (S : SelectorState P h) : Nonempty (CheckpointCertificate P) := by
  have claim : ∀ r : ℕ, ∀ h : Fin (m + 1), m - h.val = r →
      Nonempty (SelectorState P h) → Nonempty (CheckpointCertificate P) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro h heq ⟨S⟩
      rcases step h S with hdone | ⟨s, hhs, hs⟩
      · exact hdone
      · exact ih (m - s.val) (by have := s.isLt; change h.val < s.val at hhs; omega)
          s rfl hs
  exact claim (m - h.val) h rfl ⟨S⟩

end AtomicProfile
end ConsistentSubmodular
