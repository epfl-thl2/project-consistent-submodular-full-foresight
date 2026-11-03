module

public import ConsistentSubmodular.Deterministic.Reduction.ProtectedClock

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

def transferThreshold (N H : ℕ) : ℕ := N * (H + 2 * (4 * N + 1) + 2)

/-- Integer capacities and block lengths, with enough room for forced
elements, the rolling buffer, and a temporary extra insertion. These are the
parameters `κ`, `b`, `J`, and `ℓ` of Appendix B.2.4 for `η = 1/N`, here `core`,
`block`, `candidates`, and `interval`; `transferParameters` takes
`b = ⌊k/N⌋`, `J = 4N + 1`, `ℓ = ⌊b/J⌋`, and `κ = k - 10 b`. -/
structure TransferParameters (N H k : ℕ) where
  core : ℕ
  block : ℕ
  candidates : ℕ
  interval : ℕ
  core_le : core ≤ k
  core_large : H ≤ core
  block_pos : 0 < block
  heavy_le_block : H ≤ block
  interval_pos : 0 < interval
  fit : candidates * interval ≤ block
  candidates_pos : 1 ≤ candidates
  growth : 3 ≤ ((candidates - 1 : ℕ) : ℝ) * ((1 : ℝ) / N)
  capacity : core + block + H + 4 * block + 1 ≤ k
  rounding_slack : (core : ℝ) / N ≤ block
  thinning : (1 - 10 * ((1 : ℝ) / N)) * k ≤ (core : ℝ)
  enough_time : k ≤ 4 * N * candidates * interval
  candidates_eq : candidates = 4 * N + 1

def transferParameters (N H k : ℕ) (hN : 200 ≤ N)
    (hk : transferThreshold N H ≤ k) : TransferParameters N H k := by
  let b := k / N
  let J := 4 * N + 1
  let ell := b / J
  let κ := k - 10 * b
  have hN0 : 0 < N := by omega
  have hJ0 : 0 < J := by dsimp [J]; omega
  have hbfull : H + 2 * J + 2 ≤ b := by
    apply (Nat.le_div_iff_mul_le hN0).mpr
    dsimp [transferThreshold, J] at hk ⊢
    nlinarith
  have hbH : H ≤ b := by omega
  have hbJ : 2 * J ≤ b := by omega
  have hb0 : 0 < b := by omega
  have hbN : b * N ≤ k := Nat.div_mul_le_self k N
  have hb20 : 20 * b ≤ k := by nlinarith
  have hb10 : 10 * b ≤ k := by omega
  have hκ : κ + 10 * b = k := by dsimp [κ]; omega
  have hell : 2 ≤ ell := (Nat.le_div_iff_mul_le hJ0).mpr (by nlinarith)
  have hfit : J * ell ≤ b := by simpa [ell, Nat.mul_comm] using Nat.div_mul_le_self b J
  have hkbound : k < N * (b + 1) := Nat.lt_mul_div_succ k hN0
  have hbbound : b < J * (ell + 1) := Nat.lt_mul_div_succ b hJ0
  have ht1 : b + 1 ≤ 2 * J * ell := by nlinarith
  have ht2 : N * (b + 1) ≤ N * (2 * J * ell) := Nat.mul_le_mul_left N ht1
  have htime : k ≤ 4 * N * J * ell := by nlinarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  refine {
    core := κ
    block := b
    candidates := J
    interval := ell
    core_le := by omega
    core_large := by omega
    block_pos := hb0
    heavy_le_block := hbH
    interval_pos := by omega
    fit := hfit
    candidates_pos := by omega
    growth := ?_
    capacity := by omega
    rounding_slack := ?_
    thinning := ?_
    enough_time := htime
    candidates_eq := rfl }
  · have heq : J - 1 = 4 * N := by simp [J]
    rw [heq]
    push_cast
    have hid : (4 * (N : ℝ)) * (1 / N) = 4 := by field_simp
    rw [hid]
    norm_num
  · have hbNlarge : N ≤ 10 * b := by dsimp [J] at hbfull; nlinarith
    have hcN : κ ≤ b * N := by nlinarith
    apply (div_le_iff₀ hNr).mpr
    exact_mod_cast hcN
  · have heq : (κ : ℝ) + 10 * (b : ℝ) = k := by exact_mod_cast hκ
    have hbNr : (b : ℝ) * N ≤ k := by exact_mod_cast hbN
    have hh := congrArg (fun x : ℝ => x * N) heq
    have hid : (1 - 10 * ((1 : ℝ) / N)) * k * N = ((N : ℝ) - 10) * k := by
      field_simp
    have hmul : (1 - 10 * ((1 : ℝ) / N)) * k * N ≤ (κ : ℝ) * N := by
      rw [hid]
      nlinarith only [hh, hbNr]
    exact (mul_le_mul_iff_left₀ hNr).mp (by simpa only [mul_comm] using hmul)

theorem TransferParameters.list_fits {N H k : ℕ} (p : TransferParameters N H k) (L : ℕ) :
    L * p.core ≤ (4 * N * p.candidates * L) * p.interval := by
  have h := Nat.mul_le_mul_left L (p.core_le.trans p.enough_time)
  nlinarith

theorem stable_slack_comparison (α η : ℝ) (hα : α ≤ 1) (hη : 0 ≤ η) :
    (α - 14 * η) * (1 + η) ≤ (α - 2 * η) * (1 - 10 * η) := by
  nlinarith [sq_nonneg η, mul_nonneg hη (sub_nonneg.mpr hα)]

end ConsistentSubmodular
