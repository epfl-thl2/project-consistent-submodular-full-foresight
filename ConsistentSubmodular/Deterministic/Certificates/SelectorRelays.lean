module

public import ConsistentSubmodular.Deterministic.Certificates.ProfileEligibility
public import ConsistentSubmodular.Deterministic.Certificates.RelayProfiles

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem selector_envelope (hP : P.Canonical) (h : Fin (m + 1)) :
    ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h (P.rawEnvelope h) t := by
  classical
  intro t ht ha
  exact P.rawEnvelope_valid hP h t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ha⟩)

def relayState (hP : P.Canonical) (h s : Fin (m + 1)) (S : SelectorState P h)
    (hhs : h < s) (ha : P.Active s)
    (hq1 : 1 ≤ P.rawEnvelope h)
    (hd : 0 < P.designated h - P.residual h s)
    (heq : P.rawRatio h s = P.rawEnvelope h)
    (hsafe : P.PessimisticSafeEdge h s) (hhigh : (3 : ℝ) / 4 < P.designated s)
    (hfactual : P.rawEnvelope h ≤ 2 → ∀ t, h < t → P.Active t →
      0 ≤ P.actualEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h) <
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3))
    (hfsuff : 2 < P.rawEnvelope h → ∀ t, h < t → P.Active t →
      0 ≤ P.suffEligibility h (P.rawEnvelope h) t →
      P.rawEnvelope h * (P.benchmark t - P.designated h) <
        2 * P.designated h * P.rawEnvelope h - 3 * (4 * P.designated h - 3))
    (hsmall : P.rawEnvelope h < 4 / 3 → 33 / 40 ≤ P.designated h) :
    SelectorState P s := by
  let H : RelayHistory P s := {
    parent := h
    advances := hhs
    child_active := ha
    parameter := P.rawEnvelope h
    parameter_ge_one := hq1
    parameter_lt_three := P.rawEnvelope_lt_three hP h (fun _ _ => Or.inl S.below_unit)
    parent_high := S.high
    parent_access := S.access
    parent_credit := S.credit
    envelope := P.selector_envelope hP h
    denominator := hd
    attaining := heq
    safe_edge := hsafe
    failed_actual := hfactual
    failed_suff := hfsuff
    small_parameter_high_anchor := hsmall }
  exact {
    high := hhigh
    below_unit := (P.designated_antitone hP hhs.le).trans_lt S.below_unit
    access := H.child_access
    credit := H.child_credit hP
    history := H }

theorem selector_large_parameter (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq : (4 : ℝ) / 3 ≤ P.rawEnvelope h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  classical
  let q := P.rawEnvelope h
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqpos : 0 < q := by linarith
  have hq3 : q < 3 := P.rawEnvelope_lt_three hP h (fun _ _ => Or.inl S.below_unit)
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h hqpos
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
  have helig := P.attainer_suff_of_fourThirds hP h s hhs.le S.high.le S.credit
    q hq hq3 hd heq
  have henv := P.selector_envelope hP h
  by_cases hq2 : q ≤ 2
  · rcases P.actual_test hP h S.access q hq1 hq2 henv with hyes | hno
    · exact Or.inl hyes
    · have hf := hno s hhs ha (P.suff_implies_actual h s q helig)
      obtain ⟨hsafe, hhigh, _⟩ := P.fourThirds_profile_relay hP h s hhs S.high
        S.credit q hq hq2 hd heq hf
      right
      exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq1 hd heq hsafe hhigh
        (fun _ => hno) (fun hn => False.elim (not_lt_of_ge hq2 hn))
        (fun hn => False.elim (not_lt_of_ge hq hn))⟩⟩
  · rcases P.suff_test hP h S.access q (by linarith) hq3.le henv with hyes | hno
    · exact Or.inl hyes
    · have hf := hno s hhs ha helig
      obtain ⟨hsafe, hhigh, _⟩ := P.high_parameter_profile_relay hP h s hhs S.high
        S.credit q (by linarith) hd heq hf
      right
      exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq1 hd heq
        (fun z _ _ => (hsafe z).le) hhigh
        (fun hn => False.elim (hq2 hn)) (fun _ => hno)
        (fun hn => False.elim (not_lt_of_ge hq hn))⟩⟩

theorem selector_high_anchor (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq : 1 ≤ P.rawEnvelope h) (hq2 : P.rawEnvelope h ≤ 2)
    (hA : (33 : ℝ) / 40 ≤ P.designated h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by
  classical
  let q := P.rawEnvelope h
  obtain ⟨s, hs, hd, heq⟩ := P.rawEnvelope_attained h (show 0 < q by dsimp [q]; linarith)
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have ha : P.Active s := (Finset.mem_filter.mp hs).2.2
  have helig := P.high_anchor_profile_eligible hP h s hhs.le hA S.credit q hq hq2 hd heq
  rcases P.actual_test hP h S.access q hq hq2 (P.selector_envelope hP h) with hyes | hno
  · exact Or.inl hyes
  · have hf := hno s hhs ha helig
    obtain ⟨hsafe, hhigh, _⟩ := P.high_anchor_profile_relay hP h s hhs hA S.below_unit
      S.credit q hq hd heq hf
    right
    exact ⟨s, hhs, ⟨P.relayState hP h s S hhs ha hq hd heq hsafe hhigh
      (fun _ => hno) (fun hn => False.elim (not_lt_of_ge hq2 hn)) (fun _ => hA)⟩⟩

end AtomicProfile
end ConsistentSubmodular
