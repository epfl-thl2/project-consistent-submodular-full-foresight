module

public import ConsistentSubmodular.Randomized.Impossibility.HardStream
public import ConsistentSubmodular.Randomized.Impossibility.HardScalar

@[expose] public section

/-!
# Impossibility for randomized algorithms (Theorem 1 and Remark 1)

The proof of Theorem 1 in Appendix A.2, on the stream of `HardStream`.

* *Bounding the approximation ratio.* Take the weights `1, u₁, u₂` of
  Figure 2, with `u₁` the root of `Φ` in `(0, 1)` and `u₂ = u₁² (1 + u₁)`. Fix
  a randomized `C`-consistent algorithm and let `k₀, k₁, k₂` be the expected
  numbers of singleton sets of the three groups that it holds just before `U₀`
  arrives. Consistency bounds its expected value at the three last times by
  affine functions of `k₀, k₁, k₂` (`realization_bounds`), and the convex
  combination with `μ₀ = u₂`, `μ₁ = u₂/u₁ - u₂`, and `μ₂ = 1 - u₂/u₁`
  contradicts a ratio above `ξ⋆ + 12 ε` at all three times (`weighted_main`
  with `lp_bound`).
* *Removing the weights.* The rational weights `ũ_i = ⌊u_i D⌋ / D` with
  `D = ⌈1/ε⌉` satisfy `|ũ_i - u_i| ≤ ε`, so the weighted coverage of every
  family changes by at most `2 ε k`. The competitors are worth at least `k`,
  so a ratio bound `ρ ≤ 1` at the exact weights gives `ρ + 4 ε` at the
  rational weights. Multiplying all weights by `D` and replacing every cell by
  unit-weight copies keeps all ratios (`coverage_streamCover`).

Theorem 1 holds with `K = 16`; when `ξ⋆ + 16 ε ≥ 1`, one set that covers
everything already gives the bound. The formal proof keeps the errors of
consistency and of the exact cardinality constraint apart instead of merging
them into `ε̂ = ε + 1/k`, and of the rational weights it uses only
`|ũ_i - u_i| ≤ ε`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace ConsistentSubmodular.HardInstance

/-! ### Expectations -/

/-- Expectation is monotone on the realizations of positive probability. -/
theorem expectation_le_of {n : ℕ} (μ : RandomTrajectory n)
    {G H : (Fin (n + 1) → Finset (Fin n)) → ℝ} (h : ∀ S, μ.prob S ≠ 0 → G S ≤ H S) :
    ∑ S, μ.prob S * G S ≤ ∑ S, μ.prob S * H S := by
  refine Finset.sum_le_sum fun S _ => ?_
  by_cases hS : μ.prob S = 0
  · simp [hS]
  · exact mul_le_mul_of_nonneg_left (h S hS) (μ.prob_nonneg S)

/-- The expectation of an affine function of three counts. -/
theorem expectation_affine {n : ℕ} (μ : RandomTrajectory n) (a b₀ b₁ b₂ : ℝ)
    (c₀ c₁ c₂ : (Fin (n + 1) → Finset (Fin n)) → ℝ) :
    ∑ S, μ.prob S * (a + b₀ * c₀ S + b₁ * c₁ S + b₂ * c₂ S) =
      a + b₀ * ∑ S, μ.prob S * c₀ S + b₁ * ∑ S, μ.prob S * c₁ S +
        b₂ * ∑ S, μ.prob S * c₂ S := by
  have h : ∀ S, μ.prob S * (a + b₀ * c₀ S + b₁ * c₁ S + b₂ * c₂ S) =
      a * μ.prob S + b₀ * (μ.prob S * c₀ S) + b₁ * (μ.prob S * c₁ S) +
        b₂ * (μ.prob S * c₂ S) := fun S => by ring
  simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, μ.prob_sum, mul_one]

/-! ### The three last times of the stream -/

/-- Time `3k`: all tiny sets have arrived, `U₀` has not. -/
def timeBefore (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k, by omega⟩

/-- Time `3k + 1`: `U₀` has arrived. -/
def timeMiddle (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k + 1, by omega⟩

/-- Time `3k + 2`: `U₁` has arrived. -/
def timeAfter (k : ℕ) : Fin (3 * k + 2 + 1) := ⟨3 * k + 2, by omega⟩

/-- The bounds of Appendix A.2 for one realization. With `c_g` the number of tiny
sets of group `g` held at time `3k`: `ALG₀ ≤ Σ_g u_g c_g`; at most `C` sets are
inserted at each update, and each new set outside `U₀` has weight at most
`u₁`, so `ALG₁ ≤ k u₀ + u₁ c₁ + u₂ c₂ + u₁ C` and
`ALG₂ ≤ k u₀ + k u₁ + u₂ (c₂ + 2C)`; and `c₀ + c₁ + c₂ ≤ k`. -/
theorem realization_bounds {k C : ℕ} {u : Fin 3 → ℝ} (hu : ∀ g, 0 ≤ u g)
    (hu21 : u 2 ≤ u 1) {S : Fin (3 * k + 2 + 1) → Finset (Fin (3 * k + 2))}
    (hS : FeasibleTrajectory k C S) :
    weightedValue k u (S (timeBefore k)) ≤
        u 0 * tinyCount k 0 (S (timeBefore k)) + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeMiddle k)) ≤
        u 0 * k + u 1 * C + u 1 * tinyCount k 1 (S (timeBefore k)) +
          u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      weightedValue k u (S (timeAfter k)) ≤
        u 0 * k + u 1 * k + 2 * u 2 * C + u 2 * tinyCount k 2 (S (timeBefore k)) ∧
      (tinyCount k 0 (S (timeBefore k)) : ℝ) + tinyCount k 1 (S (timeBefore k)) +
        tinyCount k 2 (S (timeBefore k)) ≤ k := by
  obtain ⟨-, hsets, hrec⟩ := hS
  have hrec₁ : recourse (S (timeMiddle k)) (S (timeBefore k)) ≤ C := hrec ⟨3 * k, by omega⟩
  have hrec₂ : recourse (S (timeAfter k)) (S (timeMiddle k)) ≤ C := hrec ⟨3 * k + 1, by omega⟩
  have hbefore : ∀ e ∈ S (timeBefore k), e.val < 3 * k := fun e he =>
    (mem_filter.mp ((hsets (timeBefore k)).1 he)).2
  have hmiddle : ∀ e ∈ S (timeMiddle k), e.val < 3 * k + 1 := fun e he =>
    (mem_filter.mp ((hsets (timeMiddle k)).1 he)).2
  -- Counts of the insertions at the two updates.
  have a₁ := tinyCount_le_add (S (timeBefore k)) (S (timeMiddle k)) 1
  have a₂ := tinyCount_le_add (S (timeBefore k)) (S (timeMiddle k)) 2
  have a₁₂ := (tinyCount_sdiff_le (S (timeBefore k)) (S (timeMiddle k))).trans hrec₁
  have b₂ := tinyCount_le_add (S (timeMiddle k)) (S (timeAfter k)) 2
  have b₁₂ := (tinyCount_sdiff_le (S (timeMiddle k)) (S (timeAfter k))).trans hrec₂
  have hcard := (tinyCount_sum_le (S (timeBefore k))).trans (hsets (timeBefore k)).2
  have hw1R : 0 ≤ u 1 := hu 1
  have hw2R : 0 ≤ u 2 := hu 2
  refine ⟨value_le_before hu _ hbefore, ?_, ?_, by exact_mod_cast hcard⟩
  · have hcov := value_le_middle hu _ hmiddle
    have ha₁ : (tinyCount k 1 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 1 (S (timeBefore k)) +
        tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₁
    have ha₂ : (tinyCount k 2 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 2 (S (timeBefore k)) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₂
    have ha₁₂ : (tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) : ℝ) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) ≤ C := by exact_mod_cast a₁₂
    have h1 := mul_le_mul_of_nonneg_left ha₁ hw1R
    have h2 := mul_le_mul_of_nonneg_left ha₂ hw2R
    have h3 := mul_le_mul_of_nonneg_right hu21
      (Nat.cast_nonneg (tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k))) : (0 : ℝ) ≤ _)
    have h4 := mul_le_mul_of_nonneg_left ha₁₂ hw1R
    linarith
  · have hcov := value_le_after hu (S (timeAfter k))
    have ha₂ : (tinyCount k 2 (S (timeMiddle k)) : ℝ) ≤ tinyCount k 2 (S (timeBefore k)) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) := by exact_mod_cast a₂
    have ha₁₂ : (tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) : ℝ) +
        tinyCount k 2 (S (timeMiddle k) \ S (timeBefore k)) ≤ C := by exact_mod_cast a₁₂
    have hb₂ : (tinyCount k 2 (S (timeAfter k)) : ℝ) ≤ tinyCount k 2 (S (timeMiddle k)) +
        tinyCount k 2 (S (timeAfter k) \ S (timeMiddle k)) := by exact_mod_cast b₂
    have hb₁₂ : (tinyCount k 1 (S (timeAfter k) \ S (timeMiddle k)) : ℝ) +
        tinyCount k 2 (S (timeAfter k) \ S (timeMiddle k)) ≤ C := by exact_mod_cast b₁₂
    have hc₁ : (0 : ℝ) ≤ tinyCount k 1 (S (timeMiddle k) \ S (timeBefore k)) :=
      Nat.cast_nonneg _
    have hc₁' : (0 : ℝ) ≤ tinyCount k 1 (S (timeAfter k) \ S (timeMiddle k)) :=
      Nat.cast_nonneg _
    have htwo : (tinyCount k 2 (S (timeAfter k)) : ℝ) ≤
        tinyCount k 2 (S (timeBefore k)) + 2 * C := by linarith
    have h := mul_le_mul_of_nonneg_left htwo hw2R
    linarith

/-! ### Bounding the approximation ratio -/

/-- The weights `1, x, x² (1 + x)` of the three groups; at `x = u₁` they are the
weights `1, u₁, u₂` of Figure 2. -/
def lpWeights (x : ℝ) : Fin 3 → ℝ := ![1, x, lpThird x]

@[simp] theorem lpWeights_zero (x : ℝ) : lpWeights x 0 = 1 := rfl

@[simp] theorem lpWeights_one (x : ℝ) : lpWeights x 1 = x := rfl

@[simp] theorem lpWeights_two (x : ℝ) : lpWeights x 2 = lpThird x := rfl

theorem lpWeights_nonneg {x : ℝ} (hx : 0 ≤ x) (g : Fin 3) : 0 ≤ lpWeights x g := by
  fin_cases g
  · exact zero_le_one
  · exact hx
  · change 0 ≤ lpThird x
    unfold lpThird
    positivity

/-- The argument of Appendix A.2 on the stream with the weights `1, x, x² (1 + x)`:
if a ratio `ρ ≥ 0` satisfies the inequality
`k N + (μ₁ x + 2 μ₂ y) C ≤ ρ (k Den - (μ₁ x + 2 μ₂ y))` of the linear program,
then every randomized `C`-consistent algorithm has expected value at most `ρ`
times that of a competitor at one of the three last times. The competitor
covers all of `U₀`. -/
theorem weighted_main {k C : ℕ} {x ρ : ℝ} (hk : 2 ≤ k) (hx0 : 0 < x) (hx1 : x * (1 + x) ≤ 1)
    (hρ0 : 0 ≤ ρ)
    (hρ : (k : ℝ) * lpNumerator x + lpError x * C ≤ ρ * (k * lpDenominator x - lpError x))
    (μ : RandomTrajectory (3 * k + 2)) (hμ : μ.Feasible k C) :
    ∃ (t : Fin (3 * k + 2 + 1)) (A : Finset (Fin (3 * k + 2))),
      A ⊆ arrivedPrefix (3 * k + 2) t.val ∧ A.card ≤ k ∧
      (k : ℝ) ≤ (fiber (A.biUnion (elementCells k)) 0).card ∧
      μ.expectation (weightedValue k (lpWeights x)) t ≤ ρ * weightedValue k (lpWeights x) A := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hy0 : 0 ≤ lpThird x := by unfold lpThird; positivity
  have hy : 0 < lpThird x := by unfold lpThird; positivity
  have hyx : lpThird x ≤ x := by unfold lpThird; nlinarith
  have hu := lpWeights_nonneg hx0.le
  have hu21 : lpWeights x 2 ≤ lpWeights x 1 := by simpa using hyx
  have hμ₁ : 0 ≤ lpMuOne x := by
    unfold lpMuOne
    have : 0 ≤ 1 - x := by nlinarith
    positivity
  have hμ₂ : 0 ≤ lpMuTwo x := by unfold lpMuTwo; linarith
  -- The competitors of the three times and the optima `o₀, o₁, o₂`.
  have hopt₀ := value_firstCompetitor (k := k) hu
  have hopt₁ := value_secondCompetitor hu hk1
  have hopt₂ := value_thirdCompetitor hu hk
  simp only [lpWeights_zero, lpWeights_one, lpWeights_two, one_mul] at hopt₀ hopt₁ hopt₂
  have hA₀ := hcon (timeBefore k) (firstCompetitor k) firstCompetitor_arrived
    card_firstCompetitor_le (by exact_mod_cast firstCompetitor_fibers)
  have hA₁ := hcon (timeMiddle k) (secondCompetitor k) secondCompetitor_arrived
    (card_secondCompetitor_le hk1) (by exact_mod_cast (secondCompetitor_fibers (k := k)).1)
  have hA₂ := hcon (timeAfter k) (thirdCompetitor k) thirdCompetitor_arrived
    (card_thirdCompetitor_le hk) (by exact_mod_cast (thirdCompetitor_fibers (k := k)).1)
  -- The expected counts `k₀, k₁, k₂` and the bounds on `ALG₀, ALG₁, ALG₂`.
  set f := weightedValue k (lpWeights x) with hf
  set c : Fin 3 → (Fin (3 * k + 2 + 1) → Finset (Fin (3 * k + 2))) → ℝ :=
    fun g S => (tinyCount k g (S (timeBefore k)) : ℝ) with hc
  have hE₀ : μ.expectation f (timeBefore k) ≤
      0 + 1 * ∑ S, μ.prob S * c 0 S + x * ∑ S, μ.prob S * c 1 S +
        lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hE₁ : μ.expectation f (timeMiddle k) ≤
      ((k : ℝ) + x * C) + 0 * ∑ S, μ.prob S * c 0 S + x * ∑ S, μ.prob S * c 1 S +
        lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).2.1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hE₂ : μ.expectation f (timeAfter k) ≤
      ((k : ℝ) + x * k + 2 * lpThird x * C) + 0 * ∑ S, μ.prob S * c 0 S +
        0 * ∑ S, μ.prob S * c 1 S + lpThird x * ∑ S, μ.prob S * c 2 S := by
    rw [← expectation_affine]
    refine expectation_le_of μ fun S hS => ?_
    have := (realization_bounds hu hu21 (hμ S hS)).2.2.1
    simp only [lpWeights_zero, lpWeights_one, lpWeights_two] at this
    simp only [hc]
    linarith
  have hcount : ∑ S, μ.prob S * c 0 S + ∑ S, μ.prob S * c 1 S + ∑ S, μ.prob S * c 2 S ≤ k := by
    have h := expectation_affine μ 0 1 1 1 (c 0) (c 1) (c 2)
    have hle : ∑ S, μ.prob S * (0 + 1 * c 0 S + 1 * c 1 S + 1 * c 2 S) ≤
        ∑ S, μ.prob S * ((k : ℝ) + 0 * c 0 S + 0 * c 1 S + 0 * c 2 S) :=
      expectation_le_of μ fun S hS => by
        have := (realization_bounds hu hu21 (hμ S hS)).2.2.2
        simp only [hc]
        linarith
    rw [h, expectation_affine] at hle
    linarith
  set k₀ := ∑ S, μ.prob S * c 0 S
  set k₁ := ∑ S, μ.prob S * c 1 S
  set k₂ := ∑ S, μ.prob S * c 2 S
  set E₀ := μ.expectation f (timeBefore k)
  set E₁ := μ.expectation f (timeMiddle k)
  set E₂ := μ.expectation f (timeAfter k)
  -- The convex combination with `μ₀ = u₂`, `μ₁ = u₂/u₁ - u₂`, `μ₂ = 1 - u₂/u₁`.
  have hupper : lpThird x * E₀ + lpMuOne x * E₁ + lpMuTwo x * E₂ ≤
      k * lpNumerator x + lpError x * C := by
    have h₀ := mul_le_mul_of_nonneg_left hE₀ hy0
    have h₁ := mul_le_mul_of_nonneg_left hE₁ hμ₁
    have h₂ := mul_le_mul_of_nonneg_left hE₂ hμ₂
    have hc' := mul_le_mul_of_nonneg_left hcount hy0
    have hid : lpThird x * (0 + 1 * k₀ + x * k₁ + lpThird x * k₂) +
        lpMuOne x * (((k : ℝ) + x * C) + 0 * k₀ + x * k₁ + lpThird x * k₂) +
        lpMuTwo x * (((k : ℝ) + x * k + 2 * lpThird x * C) + 0 * k₀ + 0 * k₁ +
          lpThird x * k₂) =
        lpThird x * (k₀ + k₁ + k₂) + (k * (lpNumerator x - lpThird x) + lpError x * C) := by
      simp only [lpError, lpNumerator, lpMuOne, lpMuTwo, lpThird]
      ring
    have hid' : lpThird x * k + (k * (lpNumerator x - lpThird x) + lpError x * C) =
        k * lpNumerator x + lpError x * C := by ring
    linarith
  have hlower : ρ * (k * lpDenominator x - lpError x) <
      lpThird x * E₀ + lpMuOne x * E₁ + lpMuTwo x * E₂ := by
    have h₀ : ρ * k < E₀ := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₀ hρ0) hA₀
    have h₁ : ρ * (k + x * (k - 1)) < E₁ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₁ hρ0) hA₁
    have h₂ : ρ * (k + x * k + lpThird x * (k - 2)) < E₂ :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hopt₂ hρ0) hA₂
    have g₀ := mul_lt_mul_of_pos_left h₀ hy
    have g₁ := mul_le_mul_of_nonneg_left h₁.le hμ₁
    have g₂ := mul_le_mul_of_nonneg_left h₂.le hμ₂
    have hid : lpThird x * (ρ * k) + lpMuOne x * (ρ * (k + x * (k - 1))) +
        lpMuTwo x * (ρ * (k + x * k + lpThird x * (k - 2))) =
        ρ * (k * lpDenominator x - lpError x) := by
      rw [lpDenominator_eq]
      unfold lpError
      ring
    linarith
  linarith

/-! ### Theorem 1 -/

/-- For `ρ ≥ 1` the bound holds trivially: one element covers the whole
universe. -/
theorem upper_large {k : ℕ} {ε ρ : ℝ} (hk : 0 < k) (hρ : 1 ≤ ρ) :
    ∃ (n u : ℕ) (cover : Fin n → Finset (Fin u)),
      ∀ μ : RandomTrajectory n, μ.Feasible k ⌊ε * k⌋₊ →
        ∃ (t : Fin (n + 1)) (A : Finset (Fin n)),
          A ⊆ arrivedPrefix n t.val ∧ A.card ≤ k ∧ 0 < coverageValue cover A ∧
          μ.expectation (coverageValue cover) t ≤ ρ * coverageValue cover A := by
  refine ⟨1, 1, fun _ => univ, fun μ _ => ⟨Fin.last 1, univ, ?_, ?_, ?_, ?_⟩⟩
  · intro e _
    exact mem_filter.mpr ⟨mem_univ _, e.isLt⟩
  · simpa using hk
  · simp [coverageValue]
  · have hcov : ∀ T : Finset (Fin 1), coverageValue (fun _ : Fin 1 => (univ : Finset (Fin 1))) T ≤ 1 :=
      fun T => by
        unfold coverageValue
        exact_mod_cast (card_le_univ _).trans (by simp)
    have hall : coverageValue (fun _ : Fin 1 => (univ : Finset (Fin 1))) univ = 1 := by
      simp [coverageValue]
    rw [hall, mul_one]
    calc μ.expectation (coverageValue fun _ => univ) (Fin.last 1)
        ≤ ∑ S, μ.prob S * 1 := Finset.sum_le_sum fun S _ =>
          mul_le_mul_of_nonneg_left (hcov _) (μ.prob_nonneg S)
      _ = 1 := by simp [μ.prob_sum]
      _ ≤ ρ := hρ

/-- Expectations keep a pointwise bound up to an additive constant. -/
theorem expectation_le_add {n : ℕ} (μ : RandomTrajectory n) {g h : Finset (Fin n) → ℝ} {c : ℝ}
    (hgh : ∀ T, g T ≤ h T + c) (t : Fin (n + 1)) :
    μ.expectation g t ≤ μ.expectation h t + c := by
  unfold RandomTrajectory.expectation
  calc ∑ S, μ.prob S * g (S t) ≤ ∑ S, μ.prob S * (h (S t) + c) :=
        Finset.sum_le_sum fun S _ => mul_le_mul_of_nonneg_left (hgh _) (μ.prob_nonneg S)
    _ = ∑ S, μ.prob S * h (S t) + c := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, μ.prob_sum, one_mul]

/-- `⌊v D⌋ / D` is within `1/D` of `v ≥ 0`. -/
theorem abs_floor_div_sub_le {v : ℝ} {D : ℕ} (hv : 0 ≤ v) (hD : 0 < (D : ℝ)) :
    |(⌊v * D⌋₊ : ℝ) / D - v| ≤ 1 / D := by
  have h1 : (⌊v * D⌋₊ : ℝ) ≤ v * D := Nat.floor_le (by positivity)
  have h2 : v * D < ⌊v * D⌋₊ + 1 := Nat.lt_floor_add_one _
  have hD' : (D : ℝ) ≠ 0 := hD.ne'
  have heq : (⌊v * D⌋₊ : ℝ) / D - v = ((⌊v * D⌋₊ : ℝ) - v * D) / D := by
    field_simp
  rw [heq, abs_div, abs_of_pos hD]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [abs_le]
  constructor <;> linarith

/-- **Theorem 1** from the constants of the hard instance: with `K = 16`, every
`ε ∈ [1/k, 1]` has an unweighted coverage stream on which every randomized
`εk`-consistent algorithm has expected value at most `(ξ⋆ + 16 ε)` times a
competitor's at some time. -/
theorem randomizedUpper_of {u₁ : ℝ} (h0 : 0 < u₁) (h1 : u₁ < 1) (hphi : phi u₁ = 0)
    (hxi : xiStar = 1 / (1 + u₁ ^ 3 * (1 + u₁))) : RandomizedUpperGoal := by
  have hξ0 : 0 ≤ xiStar := by rw [hxi]; positivity
  refine ⟨16, fun k ε hk hεk hε1 => ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hεk' : 1 ≤ ε * k := by rwa [div_le_iff₀ hkR] at hεk
  have hε0 : 0 < ε := by nlinarith
  by_cases hsmall : xiStar + 16 * ε < 1
  swap
  · exact upper_large hk (by linarith)
  have hε6 : ε ≤ 1 / 6 := by linarith
  have hs := root_sum_lt_one h0 h1 hphi
  have hk2 : 2 ≤ k := by
    have : (16 : ℝ) < k := by nlinarith
    exact_mod_cast (show (2 : ℝ) ≤ k by linarith)
  -- Bounding the approximation ratio at the exact weights `1, u₁, u₂`.
  have hC0 : (0 : ℝ) ≤ (⌊ε * k⌋₊ : ℕ) := Nat.cast_nonneg _
  have hC : ((⌊ε * k⌋₊ : ℕ) : ℝ) ≤ ε * k := Nat.floor_le (by positivity)
  have hlp := lp_bound h0 hs.le hphi hε0 hε6 hkR hεk' hC0 hC
  rw [← hxi] at hlp
  -- Removing the weights: `ũ_i = ⌊u_i D⌋ / D` with `D = ⌈1/ε⌉`, in unit-weight copies.
  set D : ℕ := ⌈1 / ε⌉₊ with hD
  have hDε : 1 / ε ≤ D := Nat.le_ceil _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le (by positivity) hDε
  have hDne : (D : ℝ) ≠ 0 := hD0.ne'
  have h1D : 1 / (D : ℝ) ≤ ε := by
    rw [div_le_iff₀ hD0]
    rw [div_le_iff₀ hε0] at hDε
    linarith
  have hy0 : 0 ≤ lpThird u₁ := by unfold lpThird; positivity
  have hy1 : lpThird u₁ ≤ 1 := by unfold lpThird; nlinarith
  let w : Fin 3 → ℕ := ![D, ⌊u₁ * D⌋₊, ⌊lpThird u₁ * D⌋₊]
  have hw0 : w 0 = D := rfl
  have hw1 : w 1 = ⌊u₁ * D⌋₊ := rfl
  have hw2 : w 2 = ⌊lpThird u₁ * D⌋₊ := rfl
  have hfloor {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : ⌊v * D⌋₊ ≤ D := by
    have : ((⌊v * D⌋₊ : ℕ) : ℝ) ≤ D :=
      (Nat.floor_le (by positivity)).trans (by nlinarith)
    exact_mod_cast this
  have hw : ∀ g, w g ≤ D := by
    intro g
    fin_cases g
    · exact le_of_eq hw0
    · exact hfloor h0.le h1.le
    · exact hfloor hy0 hy1
  let v : Fin 3 → ℝ := fun g => (w g : ℝ) / D
  have hv0 : v 0 = lpWeights u₁ 0 := by
    change ((w 0 : ℕ) : ℝ) / D = lpWeights u₁ 0
    rw [hw0, lpWeights_zero, div_self hDne]
  have hv1 : |v 1 - lpWeights u₁ 1| ≤ ε := by
    change |((w 1 : ℕ) : ℝ) / D - lpWeights u₁ 1| ≤ ε
    rw [hw1, lpWeights_one]
    exact (abs_floor_div_sub_le h0.le hD0).trans h1D
  have hv2 : |v 2 - lpWeights u₁ 2| ≤ ε := by
    change |((w 2 : ℕ) : ℝ) / D - lpWeights u₁ 2| ≤ ε
    rw [hw2, lpWeights_two]
    exact (abs_floor_div_sub_le hy0 hD0).trans h1D
  have hvnn : ∀ g, 0 ≤ v g := fun g => div_nonneg (Nat.cast_nonneg _) hD0.le
  have hcov : ∀ T, coverageValue (streamCover k D w) T = D * weightedValue k v T := by
    intro T
    rw [coverage_streamCover hw, weightedValue, weightedValue, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    change (w g : ℝ) * _ = (D : ℝ) * ((w g : ℝ) / D * _)
    field_simp
  refine ⟨3 * k + 2, Fintype.card (Fin 3 × Fin k × Fin D), streamCover k D w, fun μ hμ => ?_⟩
  obtain ⟨t, A, hA, hcard, hfib, hE⟩ := weighted_main hk2 h0 hs.le (by linarith) hlp μ hμ
  -- The competitor is worth at least `k`, and every value moves by at most `2 ε k`.
  have hAk : (k : ℝ) ≤ weightedValue k v A := by
    have h := le_weightedValue hvnn A (n₀ := k) (n₁ := 0) (n₂ := 0) hfib (Nat.cast_nonneg _)
      (Nat.cast_nonneg _)
    rw [hv0, lpWeights_zero] at h
    linarith
  have hpert : ∀ T : Finset (Fin (3 * k + 2)),
      |weightedValue k v T - weightedValue k (lpWeights u₁) T| ≤ 2 * ε * k :=
    abs_weightedValue_sub_le hv0 hv1 hv2
  have hEv : μ.expectation (weightedValue k v) t ≤
      μ.expectation (weightedValue k (lpWeights u₁)) t + 2 * ε * k :=
    expectation_le_add μ (fun T => by linarith [(abs_le.mp (hpert T)).2]) t
  have hAu : weightedValue k (lpWeights u₁) A ≤ weightedValue k v A + 2 * ε * k := by
    linarith [(abs_le.mp (hpert A)).1]
  -- The ratio moves from `ξ⋆ + 12 ε ≤ 1` by at most `4 ε`.
  have hρ0 : 0 ≤ xiStar + 12 * ε := by linarith
  have hρ1 : xiStar + 12 * ε ≤ 1 := by linarith
  have hfinal : μ.expectation (weightedValue k v) t ≤ (xiStar + 16 * ε) * weightedValue k v A := by
    have g₁ := mul_le_mul_of_nonneg_left hAu hρ0
    have g₂ : (xiStar + 12 * ε) * (2 * ε * k) ≤ 2 * ε * k :=
      mul_le_of_le_one_left (by positivity) hρ1
    have g₃ := mul_le_mul_of_nonneg_left hAk (show 0 ≤ 4 * ε by linarith)
    nlinarith
  have hEcov : μ.expectation (coverageValue (streamCover k D w)) t =
      D * μ.expectation (weightedValue k v) t := by
    unfold RandomTrajectory.expectation
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun S _ => by rw [hcov]; ring
  refine ⟨t, A, hA, hcard, ?_, ?_⟩
  · rw [hcov]
    exact mul_pos hD0 (lt_of_lt_of_le hkR hAk)
  · rw [hEcov, hcov A]
    have := mul_le_mul_of_nonneg_left hfinal hD0.le
    linarith

/-- **Remark 1** from Theorem 1: for a fixed consistency bound `C` and `δ > 0`,
take `ε` with `K ε < δ`; every sufficiently large `k` has `C ≤ ⌊ε k⌋`. -/
theorem randomizedUpperLimit_of (h : RandomizedUpperGoal) : RandomizedUpperLimitGoal := by
  intro C δ hδ
  obtain ⟨K, hK⟩ := h
  set ε : ℝ := min 1 (δ / (2 * (|K| + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hKε : K * ε < δ := by
    have hle : ε ≤ δ / (2 * (|K| + 1)) := min_le_right _ _
    have h1 : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε0.le
    have h2 : |K| * ε ≤ |K| * (δ / (2 * (|K| + 1))) :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg K)
    have h3 : |K| * (δ / (2 * (|K| + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg K]
    linarith
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt ((C + 1) / ε)
  refine ⟨k₀, fun k hk₀k => ?_⟩
  have hk : (C + 1) / ε < k := hk₀.trans_le (by exact_mod_cast hk₀k)
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := lt_trans (by positivity) hk
    exact_mod_cast this
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hεk : C + 1 < ε * k := by
    rw [div_lt_iff₀ hε0] at hk
    linarith
  have hinv : 1 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    nlinarith
  obtain ⟨n, u, cover, hcover⟩ := hK k ε hkpos hinv hε1
  refine ⟨n, u, cover, fun μ hμ => ?_⟩
  have hCfloor : C ≤ ⌊ε * k⌋₊ := Nat.le_floor (by linarith)
  have hμ' : μ.Feasible k ⌊ε * k⌋₊ := fun S hS =>
    let hF := hμ S hS
    ⟨hF.1, hF.2.1, fun t => (hF.2.2 t).trans hCfloor⟩
  obtain ⟨t, A, hA, hcard, hpos, hle⟩ := hcover μ hμ'
  refine ⟨t, A, hA, hcard, lt_of_le_of_lt hle ?_⟩
  exact mul_lt_mul_of_pos_right (by linarith) hpos

end ConsistentSubmodular.HardInstance
