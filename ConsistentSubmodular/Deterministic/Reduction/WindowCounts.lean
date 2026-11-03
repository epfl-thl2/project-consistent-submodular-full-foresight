module

public import ConsistentSubmodular.Deterministic.Reduction.RoundingBudget

@[expose] public section

/-! Test counts and uniform bounds for rounding one window with at most `S`
segments in its two paths. -/

namespace ConsistentSubmodular

def windowTestBound (N S : ℕ) : ℕ := 100 * (N + 1) ^ 2 * (S + 1)

/-- The forced-element reserve: `θ⁻¹` with `θ` of order `N⁻² / log M` for
`M` tests, as for `θ = η² / (4 log(8M))` in Appendix B.2.3. -/
def windowHeavyBound (N S : ℕ) : ℕ := 64 * N ^ 2 * logBudget (4 * windowTestBound N S)

def windowLengthBound (S : ℕ) : ℕ := 100 * S + 10

theorem windowTestBound_pos (N S : ℕ) : 0 < windowTestBound N S := by
  unfold windowTestBound
  positivity

theorem windowHeavyBound_pos {N : ℕ} (S : ℕ) (hN : 0 < N) : 0 < windowHeavyBound N S := by
  unfold windowHeavyBound
  have := one_le_logBudget (4 * windowTestBound N S)
  positivity

/-- The bound allows both node and intersection value tests, even if both
endpoints of each entry/exit path are counted separately. -/
theorem window_test_count (N S s nodes tests : ℕ) (hs : s ≤ S)
    (hnodes : nodes ≤ 8 * N * s + 2)
    (htests : tests ≤ 16 * N * s + 3 * N + 4) :
    nodes + tests ≤ windowTestBound N S := by
  have hh := Nat.mul_le_mul_left (24 * N) hs
  have hsq : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hNS : N * S ≤ (N + 1) ^ 2 * S := Nat.mul_le_mul_right S (by nlinarith)
  unfold windowTestBound
  nlinarith

/-- Markov's operation budget and both forced-set endpoint adjustments fit
in one uniform integral length coefficient. -/
theorem window_operation_count (S s κ changes cleanup : ℕ)
    (hs : s ≤ S) (hchanges : changes ≤ 8 * s * κ)
    (hcleanup : cleanup ≤ 2 * κ) :
    changes + cleanup ≤ windowLengthBound S * κ := by
  have hh := Nat.mul_le_mul_right κ (Nat.mul_le_mul_left 8 hs)
  have hextra : 0 ≤ (92 * S + 8) * κ := Nat.zero_le _
  unfold windowLengthBound
  nlinarith

theorem window_uniform_operation_count (S κ changes cleanup : ℕ)
    (hchanges : changes ≤ 8 * S * κ) (hcleanup : cleanup ≤ 2 * κ) :
    changes + cleanup ≤ windowLengthBound S * κ :=
  window_operation_count S S κ changes cleanup le_rfl hchanges hcleanup

theorem window_cost_budget (S s κ : ℕ) (hs : s ≤ S) :
    2 * (s : ℝ) * κ ≤ (8 * (S : ℝ) * κ) * (1 / 4 : ℝ) := by
  have hs' : (s : ℝ) ≤ S := by exact_mod_cast hs
  have hh := mul_le_mul_of_nonneg_right hs' (show 0 ≤ 2 * (κ : ℝ) by positivity)
  nlinarith only [hh]

theorem window_scale_positive {N S κ : ℕ} (hN : 0 < N) (hκ : windowHeavyBound N S ≤ κ) :
    0 < κ := lt_of_lt_of_le (windowHeavyBound_pos S hN) hκ

end ConsistentSubmodular
