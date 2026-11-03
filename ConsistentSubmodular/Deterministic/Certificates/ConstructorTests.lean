module

public import ConsistentSubmodular.Deterministic.Certificates.SelectorState
public import ConsistentSubmodular.Deterministic.Certificates.ActualCheckpoint
public import ConsistentSubmodular.Deterministic.Certificates.SuffConstructor
public import ConsistentSubmodular.Deterministic.Certificates.PartnerSelection

@[expose] public section

/-! Exhaustive constructor tests: a failure is retained over the entire eligible
set, not only at the last row. -/

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem actual_test (hP : P.Canonical) (h : Fin (m + 1))
    (access : AccessCertificate P h) (q : ℝ) (hq1 : 1 ≤ q) (hq2 : q ≤ 2)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → 0 ≤ P.actualEligibility h q t →
        q * (P.benchmark t - P.designated h) <
          2 * P.designated h * q - 3 * (4 * P.designated h - 3) := by
  classical
  by_cases hex : ∃ s, s ∈ P.laterActive h ∧ 0 ≤ P.actualEligibility h q s
  · obtain ⟨s, hs, he⟩ := hex
    obtain ⟨c, hc, _, hec, hlast⟩ := P.last_actual_partner h s q hs he
    have hhc : h < c := (Finset.mem_filter.mp hc).2.1
    by_cases hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
        q * (P.benchmark c - P.designated h)
    · left
      exact ⟨P.checkpoint_of_actual_middle hP h c hhc q hq1 hq2 hec henv
        (fun t hct ha => (hlast t hct ha).le) hcredit
        access.entry access.initial access.terminal access.safe access.pieces⟩
    · right
      intro t _ ht he
      have htc : t ≤ c := by
        by_contra hn
        have := hlast t (lt_of_not_ge hn) ht
        linarith
      have hm := mul_le_mul_of_nonneg_left (P.benchmark_monotone hP htc)
        (show 0 ≤ q by linarith)
      linarith
  · right
    intro t hht ht he
    exact False.elim (hex ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hht, ht⟩, he⟩)

theorem suff_test (hP : P.Canonical) (h : Fin (m + 1))
    (access : AccessCertificate P h) (q : ℝ) (hq : (3 : ℝ) / 2 ≤ q) (hq3 : q ≤ 3)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → 0 ≤ P.suffEligibility h q t →
        q * (P.benchmark t - P.designated h) <
          2 * P.designated h * q - 3 * (4 * P.designated h - 3) := by
  classical
  by_cases hex : ∃ s, s ∈ P.laterActive h ∧ 0 ≤ P.suffEligibility h q s
  · obtain ⟨s, hs, he⟩ := hex
    obtain ⟨c, hc, _, hec, hlast⟩ := P.last_suff_partner h s q hs he
    have hhc : h < c := (Finset.mem_filter.mp hc).2.1
    by_cases hcredit : 2 * P.designated h * q - 3 * (4 * P.designated h - 3) ≤
        q * (P.benchmark c - P.designated h)
    · left
      exact ⟨P.checkpoint_of_suff_constructor hP h c hhc q (by linarith) hq3 hec henv
        (fun t hct ha => (hlast t hct ha).le) (Or.inr ⟨hq, hcredit⟩)
        access.entry access.initial access.terminal access.safe access.pieces⟩
    · right
      intro t _ ht he
      have htc : t ≤ c := by
        by_contra hn
        have := hlast t (lt_of_not_ge hn) ht
        linarith
      have hm := mul_le_mul_of_nonneg_left (P.benchmark_monotone hP htc)
        (show 0 ≤ q by linarith)
      linarith
  · right
    intro t hht ht he
    exact False.elim (hex ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hht, ht⟩, he⟩)

theorem low_actual_test (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hcredit : P.StrongCredit h)
    (access : AccessCertificate P h) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (henv : ∀ t, h < t → P.Active t → 0 ≤ P.envelopeSlack h q t) :
    Nonempty (CheckpointCertificate P) ∨
      ∀ t, h < t → P.Active t → P.actualEligibility h q t < 0 := by
  classical
  by_cases hex : ∃ s, s ∈ P.laterActive h ∧ 0 ≤ P.actualEligibility h q s
  · obtain ⟨s, hs, he⟩ := hex
    obtain ⟨c, hc, _, hec, hlast⟩ := P.last_actual_partner h s q hs he
    have hhc : h < c := (Finset.mem_filter.mp hc).2.1
    have hbase := P.strongCredit_baseline hP h hA hcredit
    have hA1 := P.designated_le_one hP h
    have hbudget : 3 ≤ P.designated h + 2 * P.benchmark h := by
      unfold benchmark
      linarith
    left
    exact ⟨P.checkpoint_of_actual_low hP h c hhc q hq hq1 hec henv
      (fun t hct ha => (hlast t hct ha).le) hbudget
      access.entry access.initial access.terminal access.safe access.pieces⟩
  · right
    intro t hht ht
    by_contra hn
    exact hex ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hht, ht⟩, le_of_not_gt hn⟩

end AtomicProfile
end ConsistentSubmodular
