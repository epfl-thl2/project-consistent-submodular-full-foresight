module

public import ConsistentSubmodular.Deterministic.Reduction.UniformRoundedFamilies

@[expose] public section

/-!
# The recourse rate of Theorem 5

With accuracy `N` of order `1/ε` and compressed windows of at most
`S = (C + 1)(3N + 2)` segments, the forced-element reserves are of order
`N² log N`, as in (36) of Appendix B.2.3 with `η = 1/N`. The recourse constant
of the reduction is then at most `N³ (A_C + 800 log N)`: the exact recomputation
for budgets below the threshold `N³ log N`, and the `O(N³)` operations per
update of a transition. For `ε < 3/4` this is at most `K_C ε⁻³ log(1/ε)`.
-/

noncomputable section
namespace ConsistentSubmodular

/-- The recourse constant for accuracy `1/N` when compressed windows have at
most `S` segments. -/
def reductionRecourse (N S : ℕ) : ℕ :=
  2 * transferThreshold N (familyHeavy N S) +
    4 * N * (4 * N + 1) * (3 * familyLength S + 1) + 2

/-- The accuracy parameter for slack `ε`: an integer `N ≥ 200` with `20/N < ε`
and `N ≤ 220/ε`. -/
def accuracy (ε : ℝ) : ℕ := ⌊20 / ε⌋₊ + 200

theorem accuracy_ge (ε : ℝ) : 200 ≤ accuracy ε := Nat.le_add_left _ _

theorem accuracy_slack {ε : ℝ} (hε : 0 < ε) : 20 * ((1 : ℝ) / accuracy ε) < ε := by
  have hNpos : (0 : ℝ) < accuracy ε := by
    have := accuracy_ge ε
    exact_mod_cast (show 0 < accuracy ε by omega)
  have hN : 20 / ε < (accuracy ε : ℝ) := by
    unfold accuracy
    push_cast
    have := Nat.lt_floor_add_one (20 / ε)
    linarith
  rw [mul_one_div, div_lt_iff₀ hNpos]
  have := (div_lt_iff₀ hε).mp hN
  linarith

theorem accuracy_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : (accuracy ε : ℝ) ≤ 220 / ε := by
  unfold accuracy
  push_cast
  have hfl : (⌊20 / ε⌋₊ : ℝ) ≤ 20 / ε := Nat.floor_le (by positivity)
  have h200 : (200 : ℝ) ≤ 200 / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hsplit : (220 : ℝ) / ε = 20 / ε + 200 / ε := by ring
  linarith

theorem logBudget_le_log (x : ℕ) (hx : 1 ≤ x) : (logBudget x : ℝ) ≤ 2 * Real.log x + 1 := by
  unfold logBudget
  push_cast
  have hpow : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  have hpowr : (2 : ℝ) ^ Nat.log 2 x ≤ x := by exact_mod_cast hpow
  have hlog : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
    have h := Real.log_le_log (by positivity) hpowr
    rwa [Real.log_pow] at h
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnn : (0 : ℝ) ≤ Nat.log 2 x := Nat.cast_nonneg _
  nlinarith

theorem log_succ_le {N : ℕ} (hN : 1 ≤ N) : Real.log ((N : ℝ) + 1) ≤ 1 + Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2N : (N : ℝ) + 1 ≤ 2 * N := by linarith
  have h := Real.log_le_log (by positivity) h2N
  rw [Real.log_mul (by norm_num) (by positivity)] at h
  linarith [Real.log_two_lt_d9]

/-- The constant `A_C` of the bound `N³ (A_C + 800 log N)`. -/
def rateConstant (C : ℕ) : ℝ :=
  256 * Real.log (1200 * ((C : ℝ) + 1)) + 1034 + 31220 * ((C : ℝ) + 1)

theorem rateConstant_nonneg (C : ℕ) : 0 ≤ rateConstant C := by
  unfold rateConstant
  have h : 0 ≤ Real.log (1200 * ((C : ℝ) + 1)) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ C := Nat.cast_nonneg C
    nlinarith)
  positivity

theorem window_logBudget_le (C N : ℕ) (hN : 1 ≤ N) :
    (logBudget (4 * windowTestBound N ((C + 1) * (3 * N + 2))) : ℝ) ≤
      2 * Real.log (1200 * ((C : ℝ) + 1)) + 7 + 6 * Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hC : (1 : ℝ) ≤ (C : ℝ) + 1 := by linarith [(Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  have hnat : 4 * windowTestBound N ((C + 1) * (3 * N + 2)) ≤ 1200 * (C + 1) * (N + 1) ^ 3 := by
    unfold windowTestBound
    have h : (C + 1) * (3 * N + 2) + 1 ≤ 3 * (C + 1) * (N + 1) := by nlinarith
    calc 4 * (100 * (N + 1) ^ 2 * ((C + 1) * (3 * N + 2) + 1))
        = 400 * (N + 1) ^ 2 * ((C + 1) * (3 * N + 2) + 1) := by ring
      _ ≤ 400 * (N + 1) ^ 2 * (3 * (C + 1) * (N + 1)) := Nat.mul_le_mul_left _ h
      _ = 1200 * (C + 1) * (N + 1) ^ 3 := by ring
  have hx1 : 1 ≤ 4 * windowTestBound N ((C + 1) * (3 * N + 2)) := by
    have := windowTestBound_pos N ((C + 1) * (3 * N + 2))
    omega
  have hreal : ((4 * windowTestBound N ((C + 1) * (3 * N + 2)) : ℕ) : ℝ) ≤
      1200 * ((C : ℝ) + 1) * ((N : ℝ) + 1) ^ 3 := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by exact_mod_cast hx1) hreal
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  have hsucc := log_succ_le hN
  have hb := logBudget_le_log _ hx1
  push_cast at hlog hsucc hb
  linarith

theorem bridge_logBudget_le (N : ℕ) (hN : 1 ≤ N) :
    (logBudget (4 * (2 * N + 1)) : ℝ) ≤ 7 + 2 * Real.log N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ 4 * (2 * N + 1) := by omega
  have hreal : ((4 * (2 * N + 1) : ℕ) : ℝ) ≤ 12 * N := by push_cast; linarith
  have hlog := Real.log_le_log (by exact_mod_cast hx1) hreal
  rw [Real.log_mul (by norm_num) (by positivity)] at hlog
  have h12 : Real.log 12 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]
  have hb := logBudget_le_log _ hx1
  linarith

/-- The recourse constant is `O(N³ log N)`, uniformly for `S = (C + 1)(3N + 2)`. -/
theorem reductionRecourse_le (C N : ℕ) (hN : 1 ≤ N) :
    (reductionRecourse N ((C + 1) * (3 * N + 2)) : ℝ) ≤
      (N : ℝ) ^ 3 * (rateConstant C + 800 * Real.log N) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hw := mul_le_mul_of_nonneg_left (window_logBudget_le C N hN) hN3
  have hb := mul_le_mul_of_nonneg_left (bridge_logBudget_le N hN) hN3
  have hlist : 4 * N * (4 * N + 1) * (3 * familyLength ((C + 1) * (3 * N + 2)) + 1) ≤
      31220 * (C + 1) * N ^ 3 := by
    unfold familyLength windowLengthBound
    have h1 : 4 * N * (4 * N + 1) ≤ 20 * N ^ 2 := by nlinarith
    have h2 : 3 * (100 * ((C + 1) * (3 * N + 2)) + 10 + 10) + 1 ≤ 1561 * (C + 1) * N := by
      nlinarith
    calc 4 * N * (4 * N + 1) * (3 * (100 * ((C + 1) * (3 * N + 2)) + 10 + 10) + 1)
        ≤ 20 * N ^ 2 * (1561 * (C + 1) * N) := Nat.mul_le_mul h1 h2
      _ = 31220 * (C + 1) * N ^ 3 := by ring
  have hlistr : ((4 * N * (4 * N + 1) * (3 * familyLength ((C + 1) * (3 * N + 2)) + 1) : ℕ) : ℝ) ≤
      31220 * ((C : ℝ) + 1) * (N : ℝ) ^ 3 := by exact_mod_cast hlist
  have hsmall : 2 * (N : ℝ) * (2 * (4 * N + 1) + 2) + 2 ≤ 26 * (N : ℝ) ^ 3 := by
    have h12 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h23 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith
    have h03 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := by nlinarith
    nlinarith
  unfold reductionRecourse transferThreshold familyHeavy windowHeavyBound bridgeHeavy
  push_cast at hlistr ⊢
  unfold rateConstant
  nlinarith

/-- The constant `K_C` of Theorem 5. -/
def reductionConstant (C : ℕ) : ℝ := 220 ^ 3 * (4 * rateConstant C + 20000)

theorem reductionConstant_nonneg (C : ℕ) : 0 ≤ reductionConstant C := by
  unfold reductionConstant
  have := rateConstant_nonneg C
  positivity

theorem log_le_six_add_log_inv {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hN : 1 ≤ N)
    (hNle : (N : ℝ) ≤ 220 / ε) : Real.log N ≤ 6 + Real.log (1 / ε) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.log_le_log hNr hNle
  rw [show (220 : ℝ) / ε = 220 * (1 / ε) by ring,
    Real.log_mul (by norm_num) (by positivity)] at h
  have h220 : Real.log 220 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have he := Real.exp_one_gt_d9
    have h6 : Real.exp 6 = Real.exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h6]
    nlinarith [pow_le_pow_left₀ (by norm_num) he.le 6]
  linarith

theorem quarter_le_log_inv {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 3 / 4) :
    1 / 4 ≤ Real.log (1 / ε) := by
  have h := Real.log_le_sub_one_of_pos hε
  have hinv : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  rw [hinv]
  linarith

/-- For `ε < 3/4` the recourse constant is at most `K_C ε⁻³ log(1/ε)`. -/
theorem reductionRecourse_rate (C : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 4) :
    (reductionRecourse (accuracy ε) ((C + 1) * (3 * accuracy ε + 2)) : ℝ) ≤
      reductionConstant C * (1 / ε) ^ 3 * Real.log (1 / ε) := by
  obtain ⟨N, hNdef⟩ : ∃ N, N = accuracy ε := ⟨_, rfl⟩
  rw [← hNdef]
  have hN1 : 1 ≤ N := by rw [hNdef]; exact (show 1 ≤ 200 by norm_num).trans (accuracy_ge ε)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ 220 / ε := by rw [hNdef]; exact accuracy_le hε (by linarith)
  have hbase := reductionRecourse_le C N hN1
  have hA := rateConstant_nonneg C
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hNr
  have hlogN := log_le_six_add_log_inv hε hN1 hNle
  have hlogε := quarter_le_log_inv hε hε1.le
  have hN3 : (N : ℝ) ^ 3 ≤ (220 / ε) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hNle 3
  have hfactor : 0 ≤ rateConstant C + 800 * Real.log N := by linarith
  have hpow : 0 ≤ (220 / ε) ^ 3 := pow_nonneg (div_nonneg (by norm_num) hε.le) 3
  calc (reductionRecourse N ((C + 1) * (3 * N + 2)) : ℝ)
      ≤ (N : ℝ) ^ 3 * (rateConstant C + 800 * Real.log N) := hbase
    _ ≤ (220 / ε) ^ 3 * (rateConstant C + 800 * (6 + Real.log (1 / ε))) :=
        mul_le_mul hN3 (by linarith) hfactor hpow
    _ ≤ (220 / ε) ^ 3 * ((4 * rateConstant C + 20000) * Real.log (1 / ε)) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        nlinarith
    _ = reductionConstant C * (1 / ε) ^ 3 * Real.log (1 / ε) := by
        unfold reductionConstant
        ring

end ConsistentSubmodular
