module

public import ConsistentSubmodular.Randomized.AdaptivityGap.EqualizingDistribution

@[expose] public section

/-!
# Consecutive chains

The step of the proof of Lemma 3 (Appendix A.5) that applies the hypothesis to each chain
`g(s), g(s + 1), …, g(s + N) = 1`, with the computation from the proof of Lemma 4
(Appendix A.6). Consecutive intervals of lengths `d_0 ≥ ⋯ ≥ d_N = 1`, starting at zero, with
the equalizing distribution, whose cumulative probabilities are (5), have best fixed expected
value at most `B + 1` and expected value in hindsight at least `B + C`, where
`B = Σ_{j<N} (d_j - 1)` and `C = 1 + Σ_{j<N} (1 - d_{j+1}/d_j)`. An adaptivity gap of at
least `α` therefore gives `α (C - 1) ≤ (1 - α) (1 + B)`, the bound `C - 1 ≤ q_α (1 + B)` of
the paper multiplied by `α`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Shadow

/-- The hypothesis of Lemma 3: every instance of nonincreasing consecutive intervals with the
equalizing distribution has adaptivity gap at least `α`. -/
def ChainHypothesis (α : ℝ) : Prop :=
  ∀ (N : ℕ) (I : IntervalInstance N), I.IsNonincreasingConsecutive → I.IsEqualizing →
    α ≤ I.adaptivityGap

/-- The left endpoint `ℓ_j = d_0 + ⋯ + d_{j-1}` of the `j`-th consecutive interval. -/
def chainLeft (d : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, d i

/-- The equalizing probabilities (5), with `p_0 + ⋯ + p_j = 1 / d_j`. -/
def chainProb (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1 / d 0
  | j + 1 => 1 / d (j + 1) - 1 / d j

theorem sum_chainProb (d : ℕ → ℝ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), chainProb d i = 1 / d j := by
  induction j with
  | zero => simp [chainProb]
  | succ j ih => rw [Finset.sum_range_succ, ih, chainProb]; ring

/-- Summation by parts for the mean left endpoint: `Σ_{j ≤ n} p_j ℓ_j = ℓ_n / d_n - n`. -/
theorem sum_chainProb_mul_left {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i ≤ n, d i ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), chainProb d j * chainLeft d j = chainLeft d n / d n - n := by
  induction n with
  | zero => simp [chainProb, chainLeft]
  | succ n ih =>
    have hL : chainLeft d (n + 1) = chainLeft d n + d n := Finset.sum_range_succ _ _
    rw [Finset.sum_range_succ, ih fun i hi => hd i (by omega), chainProb, hL]
    have h1 := hd n (by omega)
    have h2 := hd (n + 1) le_rfl
    field_simp
    push_cast
    ring

/-- Summation by parts for the mean length: `Σ_{j ≤ n} p_j d_j = 1 + Σ_{j<n} (1 - d_{j+1}/d_j)`. -/
theorem sum_chainProb_mul_length {d : ℕ → ℝ} {n : ℕ} (hd : ∀ i ≤ n, d i ≠ 0) :
    ∑ j ∈ Finset.range (n + 1), chainProb d j * d j =
      1 + ∑ j ∈ Finset.range n, (1 - d (j + 1) / d j) := by
  induction n with
  | zero => simp [chainProb, hd 0 le_rfl]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih fun i hi => hd i (by omega), Finset.sum_range_succ, chainProb]
    have h1 := hd n (by omega)
    have h2 := hd (n + 1) le_rfl
    field_simp
    ring

theorem sum_Iic_val {N : ℕ} (f : ℕ → ℝ) (j : Fin (N + 1)) :
    ∑ i ∈ Finset.Iic j, f i = ∑ i ∈ Finset.range (j + 1), f i := by
  have h := Finset.sum_map (Finset.Iic j) Fin.valEmbedding f
  rw [Fin.map_valEmbedding_Iic] at h
  have hI : (Finset.Iic (j : ℕ)) = Finset.range (j + 1) := by
    ext x
    simp
  rw [hI] at h
  simpa using h.symm

section

variable {N : ℕ} {d : ℕ → ℝ}

/-- The lengths of a chain ending at `d_N = 1` are at least one. -/
theorem chain_one_le (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ} (hj : j ≤ N) :
    1 ≤ d j := by
  have key : ∀ e j, j + e = N → 1 ≤ d j := by
    intro e
    induction e with
    | zero =>
      intro j h
      simp only [add_zero] at h
      subst h
      exact hN.ge
    | succ e ih =>
      intro j h
      exact (ih (j + 1) (by omega)).trans (hd j (by omega))
  exact key (N - j) j (by omega)

theorem chain_pos (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ} (hj : j ≤ N) :
    0 < d j :=
  zero_lt_one.trans_le (chain_one_le hd hN hj)

theorem chainLeft_mono (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ N + 1) : chainLeft d i ≤ chainLeft d j :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) fun k hk _ =>
    (chain_pos hd hN (by have := Finset.mem_range.mp hk; omega)).le

theorem chainProb_nonneg (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) {j : ℕ}
    (hj : j ≤ N) : 0 ≤ chainProb d j := by
  cases j with
  | zero => exact (one_div_pos.mpr (chain_pos hd hN hj)).le
  | succ j =>
    exact sub_nonneg.mpr (one_div_le_one_div_of_le (chain_pos hd hN hj) (hd j (by omega)))

/-- The consecutive intervals `[ℓ_j, ℓ_j + d_j]` of lengths `d_0, …, d_N` with the equalizing
distribution. -/
def chainInstance (N : ℕ) (d : ℕ → ℝ) (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) :
    IntervalInstance N where
  left j := chainLeft d j
  right j := chainLeft d j + d j
  prob j := chainProb d j
  left_nonneg j := Finset.sum_nonneg fun i hi =>
    (chain_pos hd hN (by have := Finset.mem_range.mp hi; have := j.isLt; omega)).le
  left_le_right j := le_add_of_nonneg_right (chain_pos hd hN (by have := j.isLt; omega)).le
  prob_nonneg j := chainProb_nonneg hd hN (by have := j.isLt; omega)
  prob_sum := by rw [Fin.sum_univ_eq_sum_range (chainProb d) (N + 1), sum_chainProb, hN, div_one]

variable (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1)

theorem chainInstance_consecutive : (chainInstance N d hd hN).IsNonincreasingConsecutive := by
  refine ⟨by simp [chainInstance, chainLeft], fun i => ?_, fun i => ?_, ?_⟩
  · simp [chainInstance, chainLeft, Finset.sum_range_succ]
  · simp only [chainInstance, Fin.val_succ, Fin.val_castSucc, add_sub_cancel_left]
    exact hd i i.isLt
  · simp [chainInstance, hN]

/-- The probabilities `chainProb` have the cumulative sums (5), so they are the equalizing
distribution of the chain. -/
theorem chainInstance_equalizing : (chainInstance N d hd hN).IsEqualizing := by
  rw [Chains.isEqualizing_iff (chainInstance_consecutive hd hN)]
  intro j
  simp only [Chains.intervalLength, chainInstance, Fin.val_last, add_sub_cancel_left, hN]
  rw [sum_Iic_val (chainProb d) j, sum_chainProb]

/-- Interval `i` gains `d_i` at the realizations `j ≤ i` and nothing later, so its expected
value is `B + d_i (p_0 + ⋯ + p_i) = B + 1`. -/
theorem chain_fixedValue_le :
    (chainInstance N d hd hN).fixedValue ≤
      ∑ j : Fin (N + 1), chainProb d j * chainLeft d j + 1 := by
  refine Finset.sup'_le _ _ fun i _ => ?_
  have hi := i.isLt
  have hdi := chain_pos hd hN (show (i : ℕ) ≤ N by omega)
  have hpoint : ∀ j : Fin (N + 1),
      chainProb d j * (chainInstance N d hd hN).value i j ≤
        chainProb d j * chainLeft d j + (if j ≤ i then chainProb d j * d i else 0) := by
    intro j
    have hp := chainProb_nonneg hd hN (show (j : ℕ) ≤ N by have := j.isLt; omega)
    simp only [chainInstance, IntervalInstance.value, mul_add]
    refine add_le_add le_rfl ?_
    split_ifs with hji
    · refine mul_le_mul_of_nonneg_left (max_le hdi.le ?_) hp
      linarith [le_max_left (chainLeft d i) (chainLeft d j)]
    · have hlt : (i : ℕ) + 1 ≤ j := by
        have := Fin.lt_def.mp (not_le.mp hji)
        omega
      have hmono := chainLeft_mono hd hN hlt (by have := j.isLt; omega)
      rw [chainLeft, Finset.sum_range_succ, ← chainLeft] at hmono
      rw [max_eq_left (by linarith [le_max_right (chainLeft d i) (chainLeft d j)]), mul_zero]
  calc _ ≤ ∑ j : Fin (N + 1), (chainProb d j * chainLeft d j +
          (if j ≤ i then chainProb d j * d i else 0)) := Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ j : Fin (N + 1), chainProb d j * chainLeft d j + 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.filter_ge_eq_Iic,
        ← Finset.sum_mul, sum_Iic_val (chainProb d) i, sum_chainProb, one_div_mul_cancel hdi.ne']

/-- At realization `j` the interval `j` itself is available, so the expected value in hindsight
is at least `Σ_j p_j (ℓ_j + d_j)`. -/
theorem chain_adaptiveValue_ge :
    ∑ j : Fin (N + 1), chainProb d j * (chainLeft d j + d j) ≤
      (chainInstance N d hd hN).adaptiveValue := by
  refine Finset.sum_le_sum fun j _ => ?_
  have hj := j.isLt
  refine mul_le_mul_of_nonneg_left ?_ (chainProb_nonneg hd hN (by omega))
  refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun i => (chainInstance N d hd hN).value i j)
    (Finset.mem_univ j))
  simp only [chainInstance, IntervalInstance.value, max_self, add_sub_cancel_left]
  rw [max_eq_right (chain_pos hd hN (show (j : ℕ) ≤ N by omega)).le]

end

/-- **The chain bound.** If consecutive intervals with the equalizing distribution have
adaptivity gap at least `α`, then every chain `d_0 ≥ ⋯ ≥ d_N = 1` satisfies
`α Σ_{j<N} (1 - d_{j+1}/d_j) ≤ (1 - α) (1 + Σ_{j<N} (d_j - 1))`. -/
theorem chain_bound {α : ℝ} (hα : 0 ≤ α) (hchain : ChainHypothesis α) {N : ℕ} {d : ℕ → ℝ}
    (hd : ∀ j < N, d (j + 1) ≤ d j) (hN : d N = 1) :
    α * ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j) ≤
      (1 - α) * (1 + ∑ j ∈ Finset.range N, (d j - 1)) := by
  have hne : ∀ i ≤ N, d i ≠ 0 := fun i hi => (chain_pos hd hN hi).ne'
  -- `B = Σ_j p_j ℓ_j = Σ_{j<N} (d_j - 1)` and `C = Σ_j p_j d_j = 1 + Σ_{j<N} (1 - d_{j+1}/d_j)`.
  have hB : ∑ j : Fin (N + 1), chainProb d j * chainLeft d j =
      ∑ j ∈ Finset.range N, (d j - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainProb d j * chainLeft d j) (N + 1),
      sum_chainProb_mul_left hne, hN, div_one, chainLeft, Finset.sum_sub_distrib]
    simp
  have hC : ∑ j : Fin (N + 1), chainProb d j * d j =
      1 + ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => chainProb d j * d j) (N + 1),
      sum_chainProb_mul_length hne]
  have hfix := chain_fixedValue_le hd hN
  have hada := chain_adaptiveValue_ge hd hN
  simp only [mul_add, Finset.sum_add_distrib] at hada
  rw [hB] at hfix hada
  rw [hC] at hada
  set B := ∑ j ∈ Finset.range N, (d j - 1)
  set S := ∑ j ∈ Finset.range N, (1 - d (j + 1) / d j)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j hj =>
    sub_nonneg.mpr (chain_one_le hd hN (by have := Finset.mem_range.mp hj; omega))
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j hj => by
    have hj := Finset.mem_range.mp hj
    rw [sub_nonneg, div_le_one (chain_pos hd hN (by omega))]
    exact hd j hj
  have hpos : 0 < (chainInstance N d hd hN).adaptiveValue := by linarith
  have hgap := hchain N _ (chainInstance_consecutive hd hN) (chainInstance_equalizing hd hN)
  rw [IntervalInstance.adaptivityGap, if_neg hpos.ne', le_div_iff₀ hpos] at hgap
  nlinarith [mul_le_mul_of_nonneg_left hada hα]

end ConsistentSubmodular.Shadow
