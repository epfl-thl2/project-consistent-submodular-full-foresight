module

public import ConsistentSubmodular.Deterministic.Certificates.CompletionScaling
public import ConsistentSubmodular.Deterministic.Certificates.FiniteCheckpoint

@[expose] public section

/-! Window instances as compatible type profiles. The mixture value of a
window is the multilinear value of its profile, so the finite checkpoint
theorem proves Theorem 7. The anchor it produces is supported on at most two
candidates. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular


/-- A point with at most two nonzero weights is supported on two labels. -/
theorem exists_two_labels_of_supportCard {m : ℕ} {p : Point m} (h : supportCard p ≤ 2) :
    ∃ a b : Fin (m + 1), ∀ i, i ≠ a → i ≠ b → p i = 0 := by
  classical
  obtain ⟨S, hSdef, hS2⟩ : ∃ S : Finset (Fin (m + 1)), (∀ i, p i ≠ 0 → i ∈ S) ∧ S.card ≤ 2 := by
    refine ⟨_, fun i hi => ?_, h⟩
    simp [hi]
  have hcases : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    refine ⟨0, 0, fun i _ _ => ?_⟩
    by_contra hi
    simpa [h0] using hSdef i hi
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    refine ⟨a, a, fun i hia _ => ?_⟩
    by_contra hi
    exact hia (Finset.mem_singleton.mp (hSdef i hi))
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
    refine ⟨a, b, fun i hia hib => ?_⟩
    by_contra hi
    rcases Finset.mem_insert.mp (hSdef i hi) with h | h
    · exact hia h
    · exact hib (Finset.mem_singleton.mp h)

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The arrivals at every natural stage, constant after the last stage. -/
def arrivalsAt (t : ℕ) : Finset (Fin n) :=
  W.arrivals ⟨min t W.lastStage, by omega⟩

theorem arrivalsAt_mono : Monotone W.arrivalsAt := by
  intro s t hst
  apply W.arrivals_mono
  change min s W.lastStage ≤ min t W.lastStage
  exact min_le_min_right _ hst

@[simp] theorem arrivalsAt_stage (j : Fin (W.lastStage + 1)) :
    W.arrivalsAt j.val = W.arrivals j := by
  unfold arrivalsAt
  congr
  have := j.isLt
  omega

/-- The compatible type profile of the window: type `i` is the candidate `O_i`. -/
def profile : CompatibleProfile (W.lastStage + 1) :=
  CompatibleProfile.fromPhysical W.objective W.candidate W.arrivalsAt W.arrivalsAt_mono

theorem mixtureValue_eq_expectation (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.mixtureValue j p = finiteExpectation p
      (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate)) := rfl

theorem mixtureValue_eq_profile (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.mixtureValue j p = W.profile.multilinearValue j.val p := by
  rw [mixtureValue_eq_expectation]
  unfold CompatibleProfile.multilinearValue profile CompatibleProfile.fromPhysical
    Objective.onTypes
  simp only [arrivalsAt_stage]

theorem benchmark_eq_profile (j : Fin (W.lastStage + 1)) :
    W.benchmark j = (W.profile.objective j.val).value {j} := by
  simp [benchmark, profile, CompatibleProfile.fromPhysical, Finset.union_comm]

theorem profile_optimal (t i : Fin (W.lastStage + 1)) :
    W.profile.residual t.val i ≤ W.profile.residual t.val t := by
  simp only [CompatibleProfile.residual, CompatibleProfile.residualOn,
    CompatibleProfile.baseline, profile, CompatibleProfile.fromPhysical,
    Objective.onTypes_singleton, Objective.onTypes_empty, arrivalsAt_stage]
  have h := W.candidate_optimal t (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  rw [Finset.union_comm (W.candidate i), Finset.union_comm (W.candidate t)] at h
  linarith

/-- A common checkpoint of the window's profile, with safe paths for the two
endpoint objectives, is a certificate. -/
def certificateOfProfile {α : ℝ} {L : ℕ} (p : Point W.lastStage)
    (entry exit : PolygonalPath W.lastStage) (hp : IsSimplex p)
    (hstage : ∀ t : Fin (W.lastStage + 1),
      α * (W.profile.objective t.val).value {t} ≤ W.profile.multilinearValue t.val p)
    (he0 : entry.node 0 = vertex 0) (he1 : entry.node (Fin.last entry.pieces) = p)
    (hx0 : exit.node 0 = p)
    (hx1 : exit.node (Fin.last exit.pieces) = vertex (Fin.last W.lastStage))
    (hentry : W.profile.SafePath 0 (α * (W.profile.objective 0).value {0}) entry)
    (hexit : W.profile.SafePath W.lastStage
      (α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage}) exit)
    (hpieces : entry.pieces + exit.pieces ≤ L) : W.Certificate α L where
  anchor := p
  entry := entry
  exit := exit
  anchor_mem := hp
  entry_mem := (show entry.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective 0).value {0} ≤ W.profile.multilinearValue 0 q) from hentry).mono
    (fun _ hq => hq.1)
  exit_mem := (show exit.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage} ≤
        W.profile.multilinearValue W.lastStage q) from hexit).mono (fun _ hq => hq.1)
  entry_start := he0
  entry_finish := he1
  exit_start := hx0
  exit_finish := hx1
  persistence j := by
    rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
    exact hstage j
  safe_entry := (show entry.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective 0).value {0} ≤ W.profile.multilinearValue 0 q) from hentry).mono
    (fun q hq => by
      rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
      exact hq.2)
  safe_exit := (show exit.Along (fun q => IsSimplex q ∧
      α * (W.profile.objective W.lastStage).value {Fin.last W.lastStage} ≤
        W.profile.multilinearValue W.lastStage q) from hexit).mono
    (fun q hq => by
      rw [W.benchmark_eq_profile, W.mixtureValue_eq_profile]
      exact hq.2)
  segments := hpieces

/-- The finite checkpoint theorem applied to the window's profile gives a
`(3/4, m + 3)`-certificate whose anchor is supported on at most two
candidates. -/
theorem exists_twoLabelCertificate :
    ∃ Z : W.Certificate (3 / 4) (W.lastStage + 3),
      ∃ a b : Fin (W.lastStage + 1), ∀ i, i ≠ a → i ≠ b → Z.anchor i = 0 := by
  obtain ⟨p, entry, exit, hp, hsupp, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    W.profile.checkpoint_for_compatible finiteCheckpoint W.profile_optimal
  exact ⟨W.certificateOfProfile p entry exit hp hstage he0 he1 hx0 hx1 hentry hexit
    (by omega), exists_two_labels_of_supportCard hsupp⟩

/-- Theorem 7 for one window. -/
theorem exists_threeQuarterCertificate :
    Nonempty (W.Certificate (3 / 4) (W.lastStage + 3)) :=
  let ⟨Z, _⟩ := W.exists_twoLabelCertificate
  ⟨Z⟩


end WindowInstance

namespace Certificates

/-- Theorem 7: every window admits a `(3/4, m + 3)`-certificate. -/
theorem threeQuarterCertificates : ThreeQuarterCertificatesGoal :=
  fun _ W => W.exists_threeQuarterCertificate

end Certificates

end ConsistentSubmodular
