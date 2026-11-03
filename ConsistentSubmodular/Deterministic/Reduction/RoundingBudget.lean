module

public import Mathlib

@[expose] public section

/-! Dimension-independent concentration budgets for the exponential tails of
Lemma B.7 (Appendix B.2.3), and one strict union bound over all tests. -/

namespace ConsistentSubmodular

/-- A binary logarithm budget: `x < 2 ^ logBudget x`. -/
def logBudget (x : ℕ) : ℕ := Nat.log 2 x + 1

theorem lt_two_pow_logBudget (x : ℕ) : x < 2 ^ logBudget x :=
  Nat.lt_pow_succ_log_self (by norm_num) x

theorem one_le_logBudget (x : ℕ) : 1 ≤ logBudget x := Nat.le_add_left 1 _

namespace RoundingBudget

/-- `exp (-c) ≤ 1 / B` once `B ≤ 2 ^ c`. -/
theorem exp_neg_le_inv_of_le_two_pow {B c : ℕ} (hB : 0 < B) (hc : B ≤ 2 ^ c) :
    Real.exp (-(c : ℝ)) ≤ 1 / B := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp c := by
    calc (2 : ℝ) ^ c ≤ Real.exp 1 ^ c := pow_le_pow_left₀ (by norm_num) h2 c
      _ = Real.exp c := by rw [← Real.exp_nat_mul, mul_one]
  have hBr : (B : ℝ) ≤ Real.exp c := (by exact_mod_cast hc : (B : ℝ) ≤ 2 ^ c).trans hpow
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by exact_mod_cast hB) hBr

/-- The cardinality tail of deviation `κ / N` fits the per-test budget once
`κ ≥ 4 N² c` and `4 B ≤ 2 ^ c`. -/
theorem size_budget_exp (B N c : ℕ) (κ : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hc : 4 * B ≤ 2 ^ c) (hκ : 4 * (N : ℝ) ^ 2 * c ≤ κ) (hκpos : 0 < κ) :
    Real.exp (-((κ / N) ^ 2) / (4 * κ)) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hexp : -((κ / N) ^ 2) / (4 * κ) = -(κ / (4 * (N : ℝ) ^ 2)) := by
    field_simp
  rw [hexp]
  have hge : (c : ℝ) ≤ κ / (4 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

/-- The lower tail of deviation `V / (4 N)` with marginal cap `V / H` and mean
bound `2 V` fits the per-test budget once `H ≥ 64 N² c` and `4 B ≤ 2 ^ c`. -/
theorem window_value_budget_exp (B N c H : ℕ) (V : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hV : 0 < V) (hH0 : 0 < H) (hc : 4 * B ≤ 2 ^ c) (hH : 64 * N ^ 2 * c ≤ H) :
    Real.exp (-((V / (4 * N)) ^ 2) / (2 * (V / H) * (2 * V))) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH0
  have hexp : -((V / (4 * N)) ^ 2) / (2 * (V / H) * (2 * V)) =
      -((H : ℝ) / (64 * (N : ℝ) ^ 2)) := by
    field_simp
    ring
  rw [hexp]
  have hge : (c : ℝ) ≤ (H : ℝ) / (64 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have := (by exact_mod_cast hH : ((64 * N ^ 2 * c : ℕ) : ℝ) ≤ H)
    push_cast at this
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

/-- The bridge lower tail of deviation `V / N` with marginal cap `2 V / H` and
mean bound `2 V` fits the per-test budget once `H ≥ 8 N² c` and `4 B ≤ 2 ^ c`. -/
theorem bridge_value_budget_exp (B N c H : ℕ) (V : ℝ) (hB : 0 < B) (hN : 0 < N)
    (hV : 0 < V) (hH0 : 0 < H) (hc : 4 * B ≤ 2 ^ c) (hH : 8 * N ^ 2 * c ≤ H) :
    Real.exp (-((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V))) ≤ 1 / (4 * B) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH0
  have hexp : -((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V)) =
      -((H : ℝ) / (8 * (N : ℝ) ^ 2)) := by
    field_simp
    ring
  rw [hexp]
  have hge : (c : ℝ) ≤ (H : ℝ) / (8 * (N : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    have := (by exact_mod_cast hH : ((8 * N ^ 2 * c : ℕ) : ℝ) ≤ H)
    push_cast at this
    linarith
  have h := exp_neg_le_inv_of_le_two_pow (B := 4 * B) (by positivity) hc
  push_cast at h
  exact (Real.exp_le_exp.mpr (neg_le_neg hge)).trans h

/-- Common per-test budget, with one quarter reserved for total operations. -/
theorem union_budget (B d e : ℝ) (hB : 0 < B) (hd : d ≤ B) (he : e ≤ B) :
    d * (1 / (4 * B)) + e * (1 / (4 * B)) + (1 : ℝ) / 4 < 1 := by
  have hp : (0 : ℝ) ≤ 1 / (4 * B) := by positivity
  have h1 := mul_le_mul_of_nonneg_right hd hp
  have h2 := mul_le_mul_of_nonneg_right he hp
  have hcancel : B * (1 / (4 * B)) = (1 : ℝ) / 4 := by field_simp
  rw [hcancel] at h1 h2
  linarith

end RoundingBudget
end ConsistentSubmodular
