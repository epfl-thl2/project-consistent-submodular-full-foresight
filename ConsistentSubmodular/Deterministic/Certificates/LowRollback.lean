module

public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackExclusions
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackBefore
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackBeforeHigh
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackEligible
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackEligibleHigh
public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackAfter
public import ConsistentSubmodular.Deterministic.Certificates.SelectorState
public import ConsistentSubmodular.Deterministic.Certificates.SuffConstructor

@[expose] public section

/-! Low-parameter rollback from the retained parent history. -/
noncomputable section
namespace ConsistentSubmodular
namespace LowRollback

variable {m aCount : ℕ}

private theorem parent_attainer_eligible (k d₀ d p W : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk3 : k < 3) (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀) (hweak : W + d₀ ≤ p) :
    (k - 1) * d + (4 - k) * d₀ ≤ W := by
  have hi : (3 - k) * (W - (k - 1) * d - (4 - k) * d₀) =
      (p - W - d₀) + (k ^ 2 - 3 * k + 3) * (d - d₀) + (3 * k - 4) * d₀ := by rw [hatt]; ring
  have h1 : 0 ≤ p - W - d₀ := by linarith
  have h2 := mul_nonneg (show 0 ≤ k ^ 2 - 3 * k + 3 by nlinarith [sq_nonneg (k - 3 / 2)])
    (sub_nonneg.mpr hd₀d)
  have h3 := mul_nonneg (show 0 ≤ 3 * k - 4 by linarith) hd₀
  have hh : 0 ≤ (3 - k) * (W - (k - 1) * d - (4 - k) * d₀) := by rw [hi]; linarith
  have := (mul_nonneg_iff_of_pos_left (show 0 < 3 - k by linarith)).mp hh
  linarith

private theorem history_ceiling (P : AtomicProfile m aCount) (h : Fin (m + 1))
    (H : RelayHistory P h) (t : Fin (m + 1)) (hat : H.parent < t)
    (ht : P.Active t) (he : ParentEligible P H.parent t H.parameter) :
    shifted P t < ceiling H.parameter (deficit P H.parent) := by
  have hf := H.suff_failure t hat ht ((parentEligible_iff P H.parent t H.parameter).mp he)
  have hk : 0 < H.parameter := lt_of_lt_of_le zero_lt_one H.parameter_ge_one
  have hc : H.parameter * ceiling H.parameter (deficit P H.parent) =
      2 * H.parameter - 3 + 3 * (4 - H.parameter) * deficit P H.parent := by
    unfold ceiling
    field_simp
  have hh : H.parameter * shifted P t < H.parameter * ceiling H.parameter (deficit P H.parent) := by
    dsimp [shifted, deficit] at *
    nlinarith only [hf, hc]
  nlinarith only [hh, hk]

/-- In the low-child branch, rollback returns the retained parent's pair.
All numerical source bounds and the attaining-row chronology are derived from
the original profile and history; the safe root entry is preserved. -/
theorem low_parameter_checkpoint (P : AtomicProfile m aCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (state : SelectorState P h)
    (hparent : 4 / 3 ≤ state.history.parameter)
    (hanchor : P.designated h < 1281 / 1600)
    (hq0 : 0 < P.rawEnvelope h) (hq1 : P.rawEnvelope h ≤ 1)
    (hno : ∀ t, h < t → P.Active t → P.actualEligibility h (P.rawEnvelope h) t < 0) :
    Nonempty (CheckpointCertificate P) := by
  classical
  let H := state.history
  let a := H.parent
  let k := H.parameter
  let q := P.rawEnvelope h
  let d₀ := deficit P a
  let d := deficit P h
  let p := shifted P h
  let pa := shifted P a
  let W := gap P a h
  have hak : a < h := H.advances
  have hk0 : 4 / 3 ≤ k := hparent
  have hk3 : k < 3 := H.parameter_lt_three
  have hkpos : 0 < k := by linarith
  have hk4 : k ≤ 4 := by linarith
  have hd₀ : 0 ≤ d₀ := sub_nonneg.mpr (P.designated_le_one hP a)
  have hd₀hi : d₀ ≤ 1 / 4 := by dsimp [d₀, deficit]; have := H.parent_high; linarith
  have hd : 319 / 1600 < d := by dsimp [d, deficit]; linarith
  have hdhi : d ≤ 1 / 4 := by dsimp [d, deficit]; have := state.high; linarith
  have hd₀d : d₀ ≤ d := deficit_monotone P hP hak.le
  have hpa : 0 ≤ pa := sub_nonneg.mpr (P.one_le_benchmark hP a)
  have hp : 0 ≤ p := sub_nonneg.mpr (P.one_le_benchmark hP h)
  have hstrong : 1 / 2 ≤ pa ∨ d₀ ≤ pa * (1 - pa) := H.parent_credit
  have hpweak : d₀ ≤ pa := strong_credit_weak d₀ pa hd₀hi hpa hstrong
  have hpW : W + pa ≤ p := by
    have hs := carrier_persistence P a h hak.le
    change 0 ≤ p - pa - W at hs
    linarith
  have hweak : W + d₀ ≤ p := by linarith
  have hatt : p = (4 - k) * W - k * d - (4 - k) * d₀ := attainment_shifted P a h k H.denominator H.attaining
  have hI := parent_floor_of_attainment k d₀ d p W hk4 hatt hweak
  have helig : ParentEligible P a h k := parent_attainer_eligible k d₀ d p W hk0 hk3 hd₀ hd₀d hatt hweak
  have hpc : p < ceiling k d₀ := history_ceiling P h H h hak H.child_active helig
  have hcredit : ∀ t, h ≤ t → Active P t → ParentEligible P a t k →
      shifted P t ≤ ceiling k d₀ := by
    intro t hht ht he
    exact (history_ceiling P h H t (hak.trans_le hht) ht he).le
  have hku : k < 40 / 17 := source_parameter_upper k d₀ d p hk0 hk3 hd.le hd₀ hI hpc
  obtain ⟨s, hs, hden, hseq⟩ := P.rawEnvelope_attained h hq0
  have hhs : h < s := (Finset.mem_filter.mp hs).2.1
  have hsactive : P.Active s := (Finset.mem_filter.mp hs).2.2
  let δ := deficit P s - deficit P h
  let Ps := shifted P s
  have hδ : 0 ≤ δ := sub_nonneg.mpr (deficit_monotone P hP hhs.le)
  have hPs : p ≤ Ps := by
    have hh := P.benchmark_monotone hP hhs.le
    dsimp [p, Ps, shifted]
    linarith
  obtain ⟨hF, hK, hJ⟩ := child_semantic_sources P hP h s hhs.le q (by dsimp [q]; linarith)
    hden hseq (hno s hhs hsactive).le
  change 0 ≤ childPersistence q d p δ Ps at hF
  change 0 ≤ childCapacity q d δ Ps at hK
  change 0 ≤ childIneligibility q d Ps at hJ
  have hElim := eliminated_child_floor q d p δ Ps hq0.le (by dsimp [q]; linarith) hF hJ
  have hChild : 0 ≤ cpoly q * d - npoly q - apoly q * p := by
    have hm := mul_nonneg (sq_nonneg q) hδ
    linarith
  have hParent : 0 ≤ (3 - k) * p - k * d - (4 - k) * (d₀ + pa) := by
    have hid : (3 - k) * p - k * d - (4 - k) * (d₀ + pa) = (4 - k) * (p - W - pa) := by rw [hatt]; ring
    rw [hid]
    exact mul_nonneg (by linarith) (by linarith)
  have hCredit : 0 ≤ 2 * k - 3 + 3 * (4 - k) * d₀ - k * p := by
    have hc : k * ceiling k d₀ = 2 * k - 3 + 3 * (4 - k) * d₀ := by unfold ceiling; field_simp
    have hm := mul_lt_mul_of_pos_left hpc hkpos
    linarith
  have hdomain : 40 / 23 < k ∧ 20 - 11 * k + (2 * k - 5) * q < 0 := by
    by_cases hkle : k ≤ 20 / 11
    · exact source_exclusions k q d₀ d p pa hk0 hkle hq0.le hq1 hpa hd₀ hd₀hi
        hstrong hParent hCredit hChild
    · refine ⟨by linarith, ?_⟩
      have hm := mul_neg_of_neg_of_pos (show 2 * k - 5 < 0 by linarith) hq0
      nlinarith
  have hR := child_deficit_floor q d p δ Ps hq0.le (by dsimp [q]; linarith) hF hK hJ
  have hU : 0 ≤ U k d₀ d p W := by
    by_cases hkle : k ≤ 20 / 11
    · exact (eligible_low_credit k d₀ d p W hdomain.1.le hkle hd.le hd₀ hd₀d hatt hweak).le
    · exact (eligible_high_credit k q d₀ d p W (by linarith) hk3 hq0 hq1 hd₀ hd₀d
        hd.le hdhi hatt hweak hpc.le hChild).le
  have hV : k ≤ 2 → 0 ≤ V k d₀ d p δ := by
    intro _
    exact (before_low_credit k q d₀ d p δ hk3 hq0 hq1 (by linarith) hd₀ hdomain.2 hI hR).le
  have hVh : 2 ≤ k → 0 ≤ VHigh k d₀ d p δ := by
    intro hk2
    exact (before_high_credit k q d₀ d p δ hk2 hk3 hq0 hq1 (by linarith) hd₀ hδ hI hR hElim).le
  have hY : 0 ≤ Y k d₀ d p δ Ps :=
    (after_credit k q d₀ d p δ Ps hdomain.1 hku hq0 hq1 hdomain.2 hd₀ hδ hI hF hK hJ).le
  have hPsC : ceiling k d₀ < Ps := attainer_credit_exceeds k q d₀ d p δ Ps hdomain.1 hk3 hq0.le
    (by linarith) hd₀ hδ hPs hI hF
  have hlate := all_later_suff_of_credits P hP a h s (ne_of_lt hak) hhs.le k
    (by linarith [hdomain.1]) hk3 hsactive hPsC hcredit hU hV hVh hY
  have hparenteligible : 0 ≤ P.suffEligibility a k h := (parentEligible_iff P a h k).mp helig
  have hstages : ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤
      P.value t (mix (vertex a) (vertex h) (k / 4)) := by
    intro t
    by_cases hht : h ≤ t
    · exact (hlate t hht).trans (P.value_mix_vertices_sufficient t a h (ne_of_lt hak)
        (by positivity) (by linarith) (le_min (P.overlap_le_left a h t) (P.overlap_le_right a h t)))
    · by_cases ht : P.Active t
      · apply P.suff_pair_prefix a h t (ne_of_lt hak) k hkpos.le hk4 (le_of_not_ge hht) hparenteligible
        by_cases hat : a < t
        · exact H.envelope t hat ht
        · exact P.envelopeSlack_early hP a t k (le_of_not_gt hat)
      · exact P.inactive_stage_safe t
          ((simplex_vertex a).mix (simplex_vertex h) (by positivity) (by linarith)) (le_of_not_gt ht)
  obtain ⟨ex, hex0, hex1, hexsafe, hexpieces⟩ := P.suff_terminal_exit hP a h (k / 4)
    (by positivity) (by linarith) (hlate (Fin.last m) (Fin.le_last h))
  let en := H.parent_access.entry
  let finalEntry := PolygonalPath.segment (vertex a) (mix (vertex a) (vertex h) (k / 4))
  have hjoin : en.node (Fin.last en.pieces) = finalEntry.node 0 := H.parent_access.terminal
  refine ⟨{
    point := mix (vertex a) (vertex h) (k / 4)
    entry := PolygonalPath.append en finalEntry
    exit := ex
    simplex := (simplex_vertex a).mix (simplex_vertex h) (by positivity) (by linarith)
    support := supportCard_mix_vertices _ _ _
    stages := hstages
    entry_initial := by rw [PolygonalPath.append_initial]; exact H.parent_access.initial
    entry_terminal := by rw [PolygonalPath.append_terminal _ _ hjoin]; exact PolygonalPath.segment_terminal _ _
    exit_initial := hex0
    exit_terminal := hex1
    entry_safe := H.parent_access.safe.append
      (P.suff_pair_entry hP a h hak k hkpos.le hk4 hparenteligible) hjoin
    exit_safe := hexsafe
    piece_budget := ?_ }⟩
  change en.pieces + 1 + ex.pieces ≤ (m + 1) + 2
  have hp := H.parent_access.pieces
  have ha := a.isLt
  dsimp [en, a] at *
  omega

end LowRollback
end ConsistentSubmodular
