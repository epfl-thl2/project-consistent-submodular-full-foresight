module

public import ConsistentSubmodular.Deterministic.Certificates.Access

@[expose] public section

/-! Retained selector history. In particular, the failed parent test is stored
for every later active eligible row, and the initial path is never discarded. -/

noncomputable section
namespace ConsistentSubmodular

variable {m atomCount : ℕ}

structure RelayHistory (P : AtomicProfile m atomCount) (child : Fin (m + 1)) where
  parent : Fin (m + 1)
  advances : parent < child
  child_active : P.Active child
  parameter : ℝ
  parameter_ge_one : 1 ≤ parameter
  parameter_lt_three : parameter < 3
  parent_high : (3 : ℝ) / 4 < P.designated parent
  parent_access : AccessCertificate P parent
  parent_credit : P.StrongCredit parent
  envelope : ∀ t, parent < t → P.Active t → 0 ≤ P.envelopeSlack parent parameter t
  denominator : 0 < P.designated parent - P.residual parent child
  attaining : P.rawRatio parent child = parameter
  safe_edge : P.PessimisticSafeEdge parent child
  /-- Below two, failure of the actual test is essential; failure of the sufficient test alone
  would be insufficient for middle rollback. -/
  failed_actual : parameter ≤ 2 → ∀ t, parent < t → P.Active t →
    0 ≤ P.actualEligibility parent parameter t →
    parameter * (P.benchmark t - P.designated parent) <
      2 * P.designated parent * parameter - 3 * (4 * P.designated parent - 3)
  failed_suff : 2 < parameter → ∀ t, parent < t → P.Active t →
    0 ≤ P.suffEligibility parent parameter t →
    parameter * (P.benchmark t - P.designated parent) <
      2 * P.designated parent * parameter - 3 * (4 * P.designated parent - 3)
  /-- The selector only relays below four thirds from a high anchor. -/
  small_parameter_high_anchor : parameter < 4 / 3 → 33 / 40 ≤ P.designated parent

namespace RelayHistory

variable {P : AtomicProfile m atomCount} {child : Fin (m + 1)}

theorem suff_failure (H : RelayHistory P child) (t : Fin (m + 1))
    (ht : H.parent < t) (ha : P.Active t) (he : 0 ≤ P.suffEligibility H.parent H.parameter t) :
    H.parameter * (P.benchmark t - P.designated H.parent) <
      2 * P.designated H.parent * H.parameter - 3 * (4 * P.designated H.parent - 3) := by
  by_cases hq : H.parameter ≤ 2
  · exact H.failed_actual hq t ht ha (P.suff_implies_actual H.parent t H.parameter he)
  · exact H.failed_suff (lt_of_not_ge hq) t ht ha he

def child_access (H : RelayHistory P child) : AccessCertificate P child :=
  P.extendAccess H.parent child H.advances H.parent_access H.safe_edge

theorem child_credit (H : RelayHistory P child) (hP : P.Canonical) : P.StrongCredit child :=
  P.strongCredit_of_pessimisticEdge hP H.parent child H.advances.le H.safe_edge

end RelayHistory

structure SelectorState (P : AtomicProfile m atomCount) (h : Fin (m + 1)) where
  high : (3 : ℝ) / 4 < P.designated h
  below_unit : P.designated h < 1
  access : AccessCertificate P h
  credit : P.StrongCredit h
  history : RelayHistory P h

end ConsistentSubmodular
