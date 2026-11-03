module

public import ConsistentSubmodular.Deterministic.Certificates.Envelope
public import ConsistentSubmodular.Deterministic.Certificates.RelayScalar

@[expose] public section

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem envelope_valid_upper (hP : P.Canonical) (h t : Fin (m + 1)) (q : ℝ)
    (hq : P.rawEnvelope h ≤ q) (ht : t ∈ P.laterActive h) :
    0 ≤ P.envelopeSlack h q t := by
  classical
  have hv := P.rawEnvelope_valid hP h t ht
  have hd := P.raw_denominator_nonnegative h t (le_of_lt (Finset.mem_filter.mp ht).2.1)
  have hm := mul_nonneg (sub_nonneg.mpr hq) hd
  unfold envelopeSlack at *
  nlinarith only [hv, hm]

theorem last_suff_partner (h s : Fin (m + 1)) (q : ℝ)
    (hs : s ∈ P.laterActive h) (he : 0 ≤ P.suffEligibility h q s) :
    ∃ c, c ∈ P.laterActive h ∧ s ≤ c ∧ 0 ≤ P.suffEligibility h q c ∧
      ∀ t, c < t → P.Active t → P.suffEligibility h q t < 0 := by
  classical
  let eligible := (P.laterActive h).filter (fun t => 0 ≤ P.suffEligibility h q t)
  have hne : eligible.Nonempty := ⟨s, Finset.mem_filter.mpr ⟨hs, he⟩⟩
  let c := eligible.max' hne
  have hc : c ∈ eligible := Finset.max'_mem _ _
  have hcle := Finset.le_max' eligible s (Finset.mem_filter.mpr ⟨hs, he⟩)
  refine ⟨c, (Finset.mem_filter.mp hc).1, hcle, (Finset.mem_filter.mp hc).2, ?_⟩
  intro t hct ht
  by_contra hn
  have htelig : t ∈ eligible := by
    refine Finset.mem_filter.mpr ⟨?_, le_of_not_gt hn⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_trans (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2.1 hct, ht⟩
  exact (not_le_of_gt hct) (Finset.le_max' eligible t htelig)

theorem root_attainer_suff (hP : P.Canonical) (s : Fin (m + 1)) (q : ℝ)
    (hs : P.designated s < 1)
    (hd : 0 < P.designated 0 - P.residual 0 s) (heq : P.rawRatio 0 s = q) :
    0 < P.suffEligibility 0 q s := by
  have hδ : 0 < 1 - P.designated s := by linarith
  have hv := P.baseline_add_residual_monotone 0 (Fin.zero_le s)
  change P.baseline 0 + P.designated 0 ≤ P.baseline s + P.residual 0 s at hv
  rw [P.baseline_zero, zero_add] at hv
  change P.designated 0 ≤ P.baseline s + P.residual 0 s at hv
  rw [hP.1] at hv
  have heq' := (div_eq_iff (ne_of_gt hd)).mp heq
  unfold rawNumerator at heq'
  rw [hP.1] at heq' hd
  have hw : 0 ≤ P.designated s - P.residual 0 s := sub_nonneg.mpr (hP.2 s 0)
  have hsq := sq_pos_of_pos hδ
  have hid : (1 - P.residual 0 s) *
      ((P.designated s - P.residual 0 s) - (q - 1) * (1 - P.designated s)) =
      (1 - P.designated s) ^ 2 -
      (1 - P.designated s) * (P.designated s - P.residual 0 s) +
      (P.designated s - P.residual 0 s) ^ 2 +
      (1 - P.designated s) * ((P.benchmark s - 1) - (P.designated s - P.residual 0 s)) := by
    have hh := congrArg (fun x : ℝ => (1 - P.designated s) * x) heq'
    nlinarith only [hh]
  have hprod := mul_nonneg hδ.le
    (show 0 ≤ (P.benchmark s - 1) - (P.designated s - P.residual 0 s) by
      unfold benchmark
      linarith)
  unfold suffEligibility
  rw [hP.1]
  nlinarith [sq_nonneg ((P.designated s - P.residual 0 s) - (1 - P.designated s) / 2)]

end AtomicProfile
end ConsistentSubmodular
