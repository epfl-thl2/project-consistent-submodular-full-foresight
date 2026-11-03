module

public import ConsistentSubmodular.Deterministic.Certificates.ActualConstructor

@[expose] public section

/-! Finite raw envelopes, with zero denominators handled before division. -/

noncomputable section
namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

def laterActive (h : Fin (m + 1)) : Finset (Fin (m + 1)) := by
  classical
  exact Finset.univ.filter (fun t => h < t ∧ P.Active t)

def rawNumerator (h t : Fin (m + 1)) : ℝ :=
  4 * (P.designated t - P.residual h t) - (P.benchmark t - P.designated h) -
    3 * (1 - P.designated h)

def rawRatio (h t : Fin (m + 1)) : ℝ :=
  P.rawNumerator h t / (P.designated h - P.residual h t)

def ratioSet (h : Fin (m + 1)) : Finset ℝ := by
  classical
  exact insert 0 ((P.laterActive h).image (P.rawRatio h))

theorem ratioSet_nonempty (h : Fin (m + 1)) : (P.ratioSet h).Nonempty := by
  classical
  exact ⟨0, Finset.mem_insert_self _ _⟩

def rawEnvelope (h : Fin (m + 1)) : ℝ :=
  (P.ratioSet h).max' (P.ratioSet_nonempty h)

theorem rawEnvelope_nonnegative (h : Fin (m + 1)) : 0 ≤ P.rawEnvelope h := by
  classical
  exact Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem rawRatio_le_envelope (h t : Fin (m + 1)) (ht : t ∈ P.laterActive h) :
    P.rawRatio h t ≤ P.rawEnvelope h := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, rfl⟩)

theorem raw_denominator_nonnegative (h t : Fin (m + 1)) (hht : h ≤ t) :
    0 ≤ P.designated h - P.residual h t := by
  have hmono := P.residual_antitone h hht
  change P.residual h t ≤ P.designated h at hmono
  exact sub_nonneg.mpr hmono

theorem raw_zero_denominator (hP : P.Canonical) (h t : Fin (m + 1)) (hht : h ≤ t)
    (hz : P.designated h - P.residual h t = 0) : P.rawNumerator h t ≤ 0 := by
  have hgt := P.designated_antitone hP hht
  have hr := hP.2 t h
  have hA := P.designated_le_one hP h
  have hL := P.baseline_nonnegative t
  unfold rawNumerator benchmark
  linarith

/-- The envelope inequality includes rows with denominator zero. -/
theorem rawEnvelope_valid (hP : P.Canonical) (h t : Fin (m + 1))
    (ht : t ∈ P.laterActive h) : 0 ≤ P.envelopeSlack h (P.rawEnvelope h) t := by
  classical
  have hht : h ≤ t := le_of_lt ((Finset.mem_filter.mp ht).2.1)
  have hden := P.raw_denominator_nonnegative h t hht
  by_cases hz : P.designated h - P.residual h t = 0
  · have hnum := P.raw_zero_denominator hP h t hht hz
    have hmul := congrArg (fun x : ℝ => P.rawEnvelope h * x) hz
    unfold envelopeSlack rawNumerator at *
    nlinarith only [hnum, hmul]
  · have hd : 0 < P.designated h - P.residual h t := lt_of_le_of_ne hden (Ne.symm hz)
    have hr := P.rawRatio_le_envelope h t ht
    have hbound := (div_le_iff₀ hd).mp hr
    unfold rawNumerator at hbound
    unfold envelopeSlack
    nlinarith only [hbound]

/-- A positive finite envelope has a genuine later active attaining row, with
a positive denominator. No omitted zero row can be selected as an attainer. -/
theorem rawEnvelope_attained (h : Fin (m + 1)) (hq : 0 < P.rawEnvelope h) :
    ∃ t, t ∈ P.laterActive h ∧ 0 < P.designated h - P.residual h t ∧
      P.rawRatio h t = P.rawEnvelope h := by
  classical
  have hmem : P.rawEnvelope h ∈ P.ratioSet h := Finset.max'_mem _ _
  rcases Finset.mem_insert.mp hmem with hz | ht
  · linarith
  · obtain ⟨t, ht, heq⟩ := Finset.mem_image.mp ht
    refine ⟨t, ht, ?_, heq⟩
    have hd := P.raw_denominator_nonnegative h t
      (le_of_lt (Finset.mem_filter.mp ht).2.1)
    by_contra hn
    have hz : P.designated h - P.residual h t = 0 := le_antisymm (le_of_not_gt hn) hd
    rw [rawRatio, hz, div_zero] at heq
    linarith

theorem rawRatio_lt_three (hP : P.Canonical) (h t : Fin (m + 1)) (hht : h ≤ t)
    (hstrict : P.designated h < 1 ∨ P.designated t < P.designated h) :
    P.rawRatio h t < 3 := by
  have hd := P.raw_denominator_nonnegative h t hht
  by_cases hz : P.designated h - P.residual h t = 0
  · simp [rawRatio, hz]
  have hdpos := lt_of_le_of_ne hd (Ne.symm hz)
  apply (div_lt_iff₀ hdpos).mpr
  have hper := P.baseline_add_residual_monotone h hht
  change P.baseline h + P.designated h ≤ P.baseline t + P.residual h t at hper
  have hL := P.baseline_nonnegative h
  have hA := P.designated_le_one hP h
  have hgt := P.designated_antitone hP hht
  unfold rawNumerator benchmark
  rcases hstrict with h | h <;> linarith

theorem rawEnvelope_lt_three (hP : P.Canonical) (h : Fin (m + 1))
    (hstrict : ∀ t, t ∈ P.laterActive h →
      P.designated h < 1 ∨ P.designated t < P.designated h) :
    P.rawEnvelope h < 3 := by
  classical
  apply (Finset.max'_lt_iff _ _).mpr
  intro r hr
  rcases Finset.mem_insert.mp hr with hr | hr
  · rw [hr]
    norm_num
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact P.rawRatio_lt_three hP h t
      (le_of_lt (Finset.mem_filter.mp ht).2.1) (hstrict t ht)

end AtomicProfile
end ConsistentSubmodular
