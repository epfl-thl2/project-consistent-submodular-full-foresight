module

public import ConsistentSubmodular.Deterministic.Certificates.LowRollbackTargets
public import ConsistentSubmodular.Deterministic.Certificates.Envelope

@[expose] public section

/-! Profile and scalar source floors for low-parameter rollback. -/

noncomputable section
namespace ConsistentSubmodular
namespace LowRollback

variable {m aCount : ℕ}

def parentFloor (k d₀ d p : ℝ) : ℝ := (3 - k) * p - k * d - 2 * (4 - k) * d₀
def childPersistence (q d p δ P : ℝ) : ℝ := (3 - q) * P - q * δ - 4 * d - (4 - q) * p
def childCapacity (q d δ P : ℝ) : ℝ := (4 - q) * (1 - d) - 4 * δ - 4 * d - P
def childIneligibility (q d P : ℝ) : ℝ := (4 - q) ^ 2 * d - (q - 2) ^ 2 - q * P

def cpoly (q : ℝ) : ℝ := (3 - q) * (4 - q) ^ 2 - 4 * q
def npoly (q : ℝ) : ℝ := (3 - q) * (q - 2) ^ 2
def apoly (q : ℝ) : ℝ := q * (4 - q)
def dpoly (q : ℝ) : ℝ := q ^ 2 - 3 * q + 3

theorem parentEligible_iff (P : AtomicProfile m aCount) (a t : Fin (m + 1)) (k : ℝ) :
    ParentEligible P a t k ↔ 0 ≤ P.suffEligibility a k t := by
  unfold ParentEligible AtomicProfile.suffEligibility deficit gap
  constructor <;> intro hi <;> nlinarith

theorem attainment_shifted (P : AtomicProfile m aCount) (a h : Fin (m + 1)) (k : ℝ)
    (hden : 0 < P.designated a - P.residual a h) (hatt : P.rawRatio a h = k) :
    shifted P h = (4 - k) * gap P a h - k * deficit P h - (4 - k) * deficit P a := by
  have heq := (div_eq_iff (ne_of_gt hden)).mp hatt
  unfold AtomicProfile.rawNumerator at heq
  unfold shifted deficit gap
  nlinarith only [heq]

theorem parent_floor_of_attainment (k d₀ d p W : ℝ)
    (hk4 : k ≤ 4) (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hp : W + d₀ ≤ p) : 0 ≤ parentFloor k d₀ d p := by
  have heq : parentFloor k d₀ d p = (4 - k) * (p - W - d₀) := by
    unfold parentFloor
    nlinarith only [hatt]
  rw [heq]
  exact mul_nonneg (sub_nonneg.mpr hk4) (by linarith)

theorem strong_credit_weak (d p : ℝ) (hd : d ≤ 1 / 4) (_hp : 0 ≤ p)
    (hstrong : 1 / 2 ≤ p ∨ d ≤ p * (1 - p)) : d ≤ p := by
  rcases hstrong with h | h
  · linarith
  · nlinarith [sq_nonneg p]

theorem child_attainment (P : AtomicProfile m aCount) (h s : Fin (m + 1)) (q : ℝ)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q) :
    shifted P s = (4 - q) * gap P h s - q * (deficit P s - deficit P h) - 4 * deficit P h := by
  have hp := attainment_shifted P h s q hden hatt
  nlinarith only [hp]

theorem child_actual_margin (P : AtomicProfile m aCount) (h s : Fin (m + 1)) (q : ℝ)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q) :
    4 * P.actualEligibility h q s =
      q * shifted P s + (q - 2) ^ 2 - (4 - q) ^ 2 * deficit P h := by
  rw [child_attainment P h s q hden hatt]
  unfold AtomicProfile.actualEligibility deficit gap
  ring

theorem child_semantic_sources (P : AtomicProfile m aCount) (_hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s) (q : ℝ) (hq4 : q ≤ 4)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q)
    (hno : P.actualEligibility h q s ≤ 0) :
    0 ≤ childPersistence q (deficit P h) (shifted P h)
      (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childCapacity q (deficit P h) (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childIneligibility q (deficit P h) (shifted P s) := by
  have heq := child_attainment P h s q hden hatt
  have hp := carrier_persistence P h s hhs
  have hc := gap_le_designated P h s
  have hmulP := mul_nonneg (sub_nonneg.mpr hq4) hp
  have hmulC := mul_nonneg (sub_nonneg.mpr hq4) (sub_nonneg.mpr hc)
  have hE := child_actual_margin P h s q hden hatt
  unfold childPersistence childCapacity childIneligibility
  dsimp [deficit] at *
  constructor
  · nlinarith only [heq, hmulP]
  constructor
  · nlinarith only [heq, hmulC]
  · linarith

theorem eliminated_child_floor (q d p δ P : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hJ : 0 ≤ childIneligibility q d P) :
    0 ≤ cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ := by
  have heq : cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ =
      q * childPersistence q d p δ P + (3 - q) * childIneligibility q d P := by
    unfold cpoly npoly apoly childPersistence childIneligibility
    ring
  rw [heq]
  exact add_nonneg (mul_nonneg hq0 hF) (mul_nonneg (sub_nonneg.mpr hq3) hJ)

theorem child_capacity_floor (q d p δ P : ℝ) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hK : 0 ≤ childCapacity q d δ P) :
    0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ := by
  have h4 : 0 < 4 - q := by linarith
  have heq : (4 - q) * ((3 - q) * (1 - d) - 4 * d - p - 3 * δ) =
      (3 - q) * childCapacity q d δ P + childPersistence q d p δ P := by
    unfold childCapacity childPersistence
    ring
  apply (mul_nonneg_iff_of_pos_left h4).mp
  rw [heq]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hq3) hK) hF

theorem child_deficit_floor (q d p δ P : ℝ) (hq0 : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ childPersistence q d p δ P) (hK : 0 ≤ childCapacity q d δ P)
    (hJ : 0 ≤ childIneligibility q d P) :
    0 ≤ (5 - 3 * q) * d - p - dpoly q * δ := by
  have hcap := child_capacity_floor q d p δ P hq3 hF hK
  have hchild := eliminated_child_floor q d p δ P hq0 hq3 hF hJ
  have heq : 4 * ((5 - 3 * q) * d - p - dpoly q * δ) =
      (q - 2) ^ 2 * ((3 - q) * (1 - d) - 4 * d - p - 3 * δ) + (cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ) := by
    unfold dpoly cpoly npoly apoly
    ring
  have hprod := mul_nonneg (sq_nonneg (q - 2)) hcap
  linarith

/-- The child attainer lies strictly beyond the failed parent's entire
eligible-credit ceiling. This is the chronology input for rollback. -/
theorem attainer_credit_exceeds (k q d₀ d p δ P : ℝ)
    (hk : 40 / 23 < k) (hk3 : k < 3) (hq : 0 ≤ q)
    (hd : 1 / 6 ≤ d) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ) (hPp : p ≤ P)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hF : 0 ≤ childPersistence q d p δ P) : ceiling k d₀ < P := by
  have hk0 : 0 < k := by linarith
  have h3 : 0 < 3 - k := by linarith
  have hqterm := mul_nonneg hq (show 0 ≤ P - p + δ by linarith)
  have hP : 4 * (p + d) ≤ 3 * P := by unfold childPersistence at hF; nlinarith only [hF, hqterm]
  have hmul := mul_le_mul_of_nonneg_left hP h3.le
  have hIfour := mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) hI
  have hfloor : 12 * d + 8 * (4 - k) * d₀ ≤ 3 * (3 - k) * P := by
    unfold parentFloor at hIfour
    nlinarith only [hmul, hIfour]
  have hkfloor := mul_le_mul_of_nonneg_left hfloor hk0.le
  have hkd := mul_le_mul_of_nonneg_left hd hk0.le
  have hC : k * ceiling k d₀ = 2 * k - 3 + 3 * (4 - k) * d₀ := by
    unfold ceiling
    field_simp
  have hCmul := congrArg (fun z : ℝ => 3 * (3 - k) * z) hC
  have hcoef : 0 ≤ (4 - k) * (17 * k - 27) * d₀ := by
    apply mul_nonneg _ hd₀
    apply mul_nonneg <;> linarith
  have hquad : 0 < 6 * k ^ 2 - 25 * k + 27 := by nlinarith [sq_nonneg (k - 25 / 12)]
  have hpos : 0 < 3 * k * (3 - k) * (P - ceiling k d₀) := by
    nlinarith only [hkfloor, hkd, hCmul, hcoef, hquad]
  have hden : 0 < 3 * k * (3 - k) := by positivity
  exact sub_pos.mp ((mul_pos_iff_of_pos_left hden).mp hpos)

end LowRollback
end ConsistentSubmodular
