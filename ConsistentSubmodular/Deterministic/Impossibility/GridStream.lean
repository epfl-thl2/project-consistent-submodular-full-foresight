module

public import ConsistentSubmodular.Deterministic.Impossibility.GridStreamCoverage

@[expose] public section

/-!
# Impossibility for deterministic algorithms (Theorem 3 and Lemma 6)

The proofs of Appendix B.1 on the stream `Σ = A ∘ B_1 ∘ ... ∘ B_m` of
Appendix B.1.1, `gridStreamCover k m`, and the impossibility for constant
recourse of Main Result 2.

Lemma 6 (Appendix B.1.2): a trajectory that maintains a `3/4`-approximation
holds `n_k ≥ 3k/4` rows once the rows have arrived (the comparison with `A` at
time `k`) and, if `m ≥ k`, at most `k/3` rows at the end of stage `k` (the
comparison with `B_k` gives `4α² - 8α + 2 ≥ 0` for `α = n_t / k`). As Remark 2
notes, the constant `1/3` only feeds the intermediate point argument.

Theorem 3 uses the stream with `m = k`. Rows enter and leave one at a time, so
some time `t > k` has `k/2 ≤ n_t < k/2 + εk`. If `t` lies in stage `j`, the
trajectory covers at most `3/4 (k + 2εk)² + kj/2` elements, while the last
complete stage `B_{j-1}`, or `A` if `j = 1`, covers `k (k + j - 1)`; the ratio
is at most `3/4 (1 + 2ε)² (k + j)/(k + j - 1) ≤ 3/4 + 6ε`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace ConsistentSubmodular.GridStream

/-- A sequence that is at least `h` at `s`, below `h` at `e`, and drops by at
most `δ` per step takes a value in `[h, h + δ)` at some time in `[s, e)`. This
is the intermediate point argument of Appendix B.1. -/
theorem exists_crossing (b : ℕ → ℝ) {h δ : ℝ} {s e : ℕ} (hse : s ≤ e) (hs : h ≤ b s)
    (he : b e < h) (hstep : ∀ t, s ≤ t → t < e → b t ≤ b (t + 1) + δ) :
    ∃ t, s ≤ t ∧ t < e ∧ h ≤ b t ∧ b t < h + δ := by
  obtain ⟨d, rfl⟩ : ∃ d, e = s + d := ⟨e - s, by omega⟩
  clear hse
  induction d generalizing s with
  | zero =>
    simp only [Nat.add_zero] at he
    linarith
  | succ d ih =>
    by_cases h1 : b (s + 1) < h
    · exact ⟨s, le_rfl, by omega, hs, by linarith [hstep s le_rfl (by omega)]⟩
    · obtain ⟨t, h1t, h2t, h3t, h4t⟩ := ih (s := s + 1) (le_of_not_gt h1)
        (by rwa [show s + 1 + d = s + (d + 1) by omega])
        (fun t ht1 ht2 => hstep t (by omega) (by omega))
      exact ⟨t, by omega, by omega, h3t, h4t⟩

section Lemma6

variable {k m C : ℕ} {S : Fin (k + m * k + 1) → Finset (Fin (k + m * k))}

/-- Part 1 of Lemma 6: once the rows have arrived, the comparison with all rows
forces `n_k ≥ 3k/4`. -/
theorem rows_at_k (hk : 0 < k) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * k ≤ 4 * rowsHeld k (S ⟨k, by omega⟩) := by
  set t₀ : Fin (k + m * k + 1) := ⟨k, by omega⟩
  have hA := happrox t₀ (arrivedPrefix (k + m * k) k) subset_rfl
    (card_arrivedPrefix (by omega)).le
  have hrows := coverage_rows (k := k) (m := m)
  have hS0 := coverage_le_rows (S t₀) (hS.2.1 t₀).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h : (3 * (k : ℝ)) * k ≤ (4 * (rowsHeld k (S t₀) : ℝ)) * k := by nlinarith
  exact_mod_cast le_of_mul_le_mul_right h hkR

/-- Part 2 of Lemma 6: at the end of stage `k`, time `k (k + 1)`, the comparison
with `B_k`, which covers `2k²`, gives `4 n² - 8 k n + 2 k² ≥ 0`, that is
`4α² - 8α + 2 ≥ 0` for `α = n / k ≤ 1`; hence `α ≤ 1 - √2/2 ≤ 1/3`. -/
theorem rows_after_stage (hk : 0 < k) (hm : k ≤ m) (hS : FeasibleTrajectory k C S)
    (happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t)) :
    3 * rowsHeld k (S ⟨k + k * k, by
      have := Nat.mul_le_mul_right k hm
      omega⟩) ≤ k := by
  have hmk := Nat.mul_le_mul_right k hm
  set t₁ : Fin (k + m * k + 1) := ⟨k + k * k, by omega⟩
  -- The competitor `B_k`, the columns of stage `k`.
  have hsub : stageColumns k m k ⊆ arrivedPrefix (k + m * k) t₁.val :=
    stageColumns_subset (le_of_eq (by simp only [t₁]; ring))
  have hA := happrox t₁ _ hsub (card_stageColumns hm).le
  have hstage := coverage_stage (k := k) (m := m) (j := k) hk hm
  -- At time `k (k + 1)` the trajectory holds column sets from the stages up to `k`.
  have hJ : (t₁.val - 1) / k = k := by
    simp only [t₁]
    rw [show k + k * k - 1 = k * k + (k - 1) by omega]
    exact (mul_add_div_mod (by omega)).1
  have hst := stage_lt_of_arrived hk (hS.2.1 t₁).1
  rw [hJ] at hst
  have hcov := coverage_le (S t₁) k (hS.2.1 t₁).2 hst
  have hn := (rowsHeld_le_card k (S t₁)).trans (hS.2.1 t₁).2
  set n := rowsHeld k (S t₁)
  have hnR : (n : ℝ) ≤ k := by exact_mod_cast hn
  -- `3/4 · 2k² ≤ n k + (k - n) 2k - n (k - n)`, that is `4 n² - 8 k n + 2 k² ≥ 0`.
  have hquad : 0 ≤ 4 * (n : ℝ) ^ 2 - 8 * k * n + 2 * k ^ 2 := by
    nlinarith
  -- With `n ≤ k` this forces `n ≤ (1 - √2/2) k ≤ k/3`.
  by_contra hcon
  have h3 : k + 1 ≤ 3 * n := by omega
  have h3R : (k : ℝ) + 1 ≤ 3 * n := by exact_mod_cast h3
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith [mul_nonneg (sub_nonneg.mpr h3R) (by linarith : (0 : ℝ) ≤ 5 * k - 1 - 3 * n)]

end Lemma6

/-- **Lemma 6** (behavior on the stream `Σ`): part 1 at time `k`, part 2 at the
end of stage `k`, time `k (k + 1) > k`. -/
theorem gridStreamCrossing : GridStreamCrossingGoal := by
  intro k m hk C S hS happrox
  refine ⟨rows_at_k hk hS happrox, fun hm => ?_⟩
  have hmk := Nat.mul_le_mul_right k hm
  exact ⟨⟨k + k * k, by omega⟩, Nat.lt_add_of_pos_right (Nat.mul_pos hk hk),
    rows_after_stage hk hm hS happrox⟩

/-- The chain of inequalities in the proof of Theorem 3 (Appendix B.1): if
`k/2 ≤ x ≤ k/2 + εk`, `j ≥ 1`, `εk ≥ 1`, and `ε < 1/4`, then the coverage bound
`x k + (k - x)(k + j) - x (k - x)` is at most `3/4 (k + 2εk)² + kj/2`, hence at
most `3/4 (1 + 2ε)² (1 + ε) k (k + j - 1) ≤ (3/4 + 6ε) k (k + j - 1)`. -/
theorem theorem3_chain {k x j ε : ℝ} (hk : 0 < k) (hx0 : k / 2 ≤ x) (hx1 : x ≤ k / 2 + ε * k)
    (hj : 1 ≤ j) (hε0 : 0 < ε) (hε4 : ε < 1 / 4) (hεk : 1 ≤ ε * k) :
    x * k + (k - x) * (k + j) - x * (k - x) ≤ (3 / 4 + 6 * ε) * (k * (k + j - 1)) := by
  have hd0 : 0 ≤ x - k / 2 := by linarith
  have hsq : (x - k / 2) ^ 2 ≤ (ε * k) ^ 2 := pow_le_pow_left₀ hd0 (by linarith) 2
  have hεkk : 0 ≤ ε * k ^ 2 := mul_nonneg hε0.le (sq_nonneg _)
  have hxj : 0 ≤ (x - k / 2) * j := mul_nonneg hd0 (by linarith)
  have hkj : 0 ≤ k * j := mul_nonneg hk.le (by linarith)
  have hsq2 : 0 ≤ (1 + 2 * ε) ^ 2 - 1 := by nlinarith
  have hkj1 : 0 ≤ k * (k + j - 1) := mul_nonneg hk.le (by linarith)
  calc x * k + (k - x) * (k + j) - x * (k - x)
      = k ^ 2 + k * j - x * j - x * k + x ^ 2 := by ring
    _ ≤ k ^ 2 + k * j - k * j / 2 - k ^ 2 / 2 + (k + 2 * ε * k) ^ 2 / 4 := by
        nlinarith only [hsq, hεkk, hxj]
    _ ≤ 3 / 4 * (k + 2 * ε * k) ^ 2 + 1 / 2 * k * j := by
        nlinarith only [hεkk, sq_nonneg (ε * k)]
    _ ≤ 3 / 4 * (1 + 2 * ε) ^ 2 * (k * (k + j)) := by
        nlinarith only [mul_nonneg hkj hsq2, hkj]
    _ ≤ 3 / 4 * (1 + 2 * ε) ^ 2 * ((1 + ε) * (k * (k + j - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith only [mul_nonneg (mul_nonneg hε0.le hk.le) (sub_nonneg.mpr hj), hεk, hk]
    _ ≤ (3 / 4 + 6 * ε) * (k * (k + j - 1)) := by
        have hpoly : 3 / 4 * (1 + 2 * ε) ^ 2 * (1 + ε) ≤ 3 / 4 + 6 * ε := by
          nlinarith only [mul_nonneg hε0.le (sub_nonneg.mpr hε4.le),
            mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr hε4.le), hε0]
        nlinarith only [mul_le_mul_of_nonneg_right hpoly hkj1]

/-- The argument of Theorem 3 (Appendix B.1) on the stream `Σ` with `m ≥ k`
stages: every trajectory with recourse `⌊εk⌋` has a time at which it covers at
most `3/4 + 6ε` times a competitor. -/
theorem exists_bad_time {k m : ℕ} {ε : ℝ} (hk : 0 < k) (hm : k ≤ m)
    (hεk : 1 / (k : ℝ) ≤ ε) (S : Fin (k + m * k + 1) → Finset (Fin (k + m * k)))
    (hS : FeasibleTrajectory k ⌊ε * k⌋₊ S) :
    ∃ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val ∧ A.card ≤ k ∧
      0 < coverageValue (gridStreamCover k m) A ∧
      coverageValue (gridStreamCover k m) (S t) ≤
        (3 / 4 + 6 * ε) * coverageValue (gridStreamCover k m) A := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hεk1 : 1 ≤ ε * k := by
    have := (div_le_iff₀ hkR).mp hεk
    linarith
  have hε0 : 0 < ε := by nlinarith
  have hmk := Nat.mul_le_mul_right k hm
  set t₀ : Fin (k + m * k + 1) := ⟨k, by omega⟩
  have hrows_card : (arrivedPrefix (k + m * k) k).card ≤ k := (card_arrivedPrefix (by omega)).le
  have hrows_cov := coverage_rows (k := k) (m := m)
  have hrows_pos : 0 < coverageValue (gridStreamCover k m) (arrivedPrefix (k + m * k) k) := by
    nlinarith
  by_cases hε4 : 1 / 4 ≤ ε
  · -- The trivial bound: at time `k` the ratio is at most `1 ≤ 3/4 + 6ε`.
    refine ⟨t₀, arrivedPrefix (k + m * k) k, subset_rfl, hrows_card, hrows_pos, ?_⟩
    have hmono := coverage_mono (gridStreamCover k m) (hS.2.1 t₀).1
    nlinarith
  push Not at hε4
  -- Otherwise the trajectory may be assumed to maintain a `3/4`-approximation.
  by_contra hno
  push Not at hno
  have happrox : ∀ (t : Fin (k + m * k + 1)) (A : Finset (Fin (k + m * k))),
      A ⊆ arrivedPrefix (k + m * k) t.val → A.card ≤ k →
      3 / 4 * coverageValue (gridStreamCover k m) A ≤
        coverageValue (gridStreamCover k m) (S t) := by
    intro t A hA hAc
    rcases (coverage_nonneg (gridStreamCover k m) A).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      exact coverage_nonneg _ _
    · have := hno t A hA hAc hpos
      nlinarith
  have h1 := rows_at_k hk hS happrox
  have h2 := rows_after_stage hk hm hS happrox
  -- The number of rows held, as a sequence indexed by time.
  set b : ℕ → ℝ := fun t =>
    if ht : t < k + m * k + 1 then (rowsHeld k (S ⟨t, ht⟩) : ℝ) else 0 with hb
  have hbt (t : ℕ) (ht : t < k + m * k + 1) : b t = rowsHeld k (S ⟨t, ht⟩) := by
    simp only [hb, dif_pos ht]
  have hfloor : (⌊ε * k⌋₊ : ℝ) ≤ ε * k := Nat.floor_le (by positivity)
  have hnk : (3 * k : ℝ) ≤ 4 * (rowsHeld k (S t₀) : ℝ) := by exact_mod_cast h1
  obtain ⟨t, hkt, hte, hlo, hhi⟩ := exists_crossing b (h := (k : ℝ) / 2)
    (δ := (⌊ε * k⌋₊ : ℝ)) (s := k) (e := k + k * k) (by omega)
    (by
      rw [hbt k (by omega)]
      linarith)
    (by
      rw [hbt _ (by omega)]
      have : 3 * (rowsHeld k (S ⟨k + k * k, by omega⟩) : ℝ) ≤ k := by
        exact_mod_cast h2
      linarith)
    (by
      intro t _ ht
      have htN : t < k + m * k := by omega
      rw [hbt t (by omega), hbt (t + 1) (by omega)]
      have hrec := hS.2.2 ⟨t, htN⟩
      have hle := rowsHeld_le_add_recourse k (S (Fin.succ ⟨t, htN⟩)) (S (Fin.castSucc ⟨t, htN⟩))
      have hle' : (rowsHeld k (S (Fin.castSucc ⟨t, htN⟩)) : ℝ) ≤
          rowsHeld k (S (Fin.succ ⟨t, htN⟩)) + ⌊ε * k⌋₊ := by
        exact_mod_cast hle.trans (Nat.add_le_add_left hrec _)
      simpa [Fin.succ_mk, Fin.castSucc_mk] using hle')
  -- The crossing time `t > k`, since `n_k ≥ 3k/4 > k/2 + εk`.
  have hεk4 : ε * k < k / 4 := by nlinarith
  have htk : k < t := by
    by_contra hcon
    have htk' : t = k := by omega
    have hbk : b t = rowsHeld k (S t₀) := by
      rw [htk']
      exact hbt k (by omega)
    linarith
  set T : Fin (k + m * k + 1) := ⟨t, by omega⟩
  rw [hbt t (by omega)] at hlo hhi
  set x : ℝ := (rowsHeld k (S T) : ℝ) with hx
  -- The stage `j = (t - 1) / k ≥ 1` of the crossing time.
  set j := (t - 1) / k with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le hk).mpr (by omega)
  have hjk : j ≤ k := Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hk).mpr (by
    rw [Nat.succ_mul]
    omega))
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  -- The trajectory covers at most `n k + (k - n)(k + j) - n (k - n)` elements.
  have hcov := coverage_le (S T) j (hS.2.1 T).2 (stage_lt_of_arrived hk (hS.2.1 T).1)
  rw [← hx] at hcov
  -- The last complete stage `B_{j-1}`, or `A` if `j = 1`, covers `k (k + j - 1)`.
  obtain ⟨A, hA, hAc, hAv⟩ : ∃ A : Finset (Fin (k + m * k)),
      A ⊆ arrivedPrefix (k + m * k) T.val ∧ A.card ≤ k ∧
      (k : ℝ) * (k + j - 1) ≤ coverageValue (gridStreamCover k m) A := by
    rcases Nat.lt_or_ge 1 j with hj2 | hj2
    · refine ⟨stageColumns k m (j - 1), stageColumns_subset ?_,
        (card_stageColumns (by omega)).le, ?_⟩
      · have hjt : j * k ≤ t - 1 := Nat.div_mul_le_self (t - 1) k
        rw [Nat.sub_add_cancel hj1]
        show j * k ≤ t
        omega
      · have hstage := coverage_stage (k := k) (m := m) (j := j - 1) (by omega) (by omega)
        rw [Nat.cast_sub hj1] at hstage
        push_cast at hstage
        linarith [show (k : ℝ) * (k + j - 1) = k * k + k * (j - 1) by ring]
    · have hj1' : j = 1 := le_antisymm hj2 hj1
      refine ⟨arrivedPrefix (k + m * k) k, arrivedPrefix_mono hkt, hrows_card, ?_⟩
      rw [hj1']
      push_cast
      linarith [show (k : ℝ) * (k + 1 - 1) = k * k by ring]
  have hApos : 0 < coverageValue (gridStreamCover k m) A := by nlinarith
  have hbad := hno T A hA hAc hApos
  -- The chain of inequalities of Appendix B.1 at the crossing time.
  have hx0 : (k : ℝ) / 2 ≤ x := by linarith
  have hx1 : x ≤ (k : ℝ) / 2 + ε * k := by linarith
  have hchain := theorem3_chain hkR hx0 hx1 hjR hε0 hε4 hεk1
  have hAv' := mul_le_mul_of_nonneg_left hAv (by linarith : (0 : ℝ) ≤ 3 / 4 + 6 * ε)
  linarith

/-- **Theorem 3** with `K = 6`, on the stream `Σ` with `m = k` stages. -/
theorem deterministicUpper : DeterministicUpperGoal :=
  ⟨6, fun k _ hk hεk _ => ⟨k + k * k, k * k + k * k, gridStreamCover k k,
    exists_bad_time hk le_rfl hεk⟩⟩

/-- The impossibility of Main Result 2 for constant recourse, from Theorem 3:
choose `ε` with `3/4 + K ε < α` and a budget `k` with `C ≤ ⌊ε k⌋`. -/
theorem deterministicUpperLimit_of (h : DeterministicUpperGoal) : DeterministicUpperLimitGoal := by
  obtain ⟨K, hK⟩ := h
  intro α hα C
  set ε : ℝ := min 1 ((α - 3 / 4) / (2 * (|K| + 1))) with hεdef
  have hgap : 0 < α - 3 / 4 := by linarith
  have hK1 : 0 < |K| + 1 := by positivity
  have hε0 : 0 < ε := lt_min one_pos (div_pos hgap (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hKε : 3 / 4 + K * ε < α := by
    have hle : ε ≤ (α - 3 / 4) / (2 * (|K| + 1)) := min_le_right _ _
    have h1 : K * ε ≤ |K| * ε := mul_le_mul_of_nonneg_right (le_abs_self K) hε0.le
    have h2 : (|K| + 1) * ε ≤ (α - 3 / 4) / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      rw [le_div_iff₀ (by positivity)] at hle
      nlinarith
    nlinarith
  obtain ⟨k, hk⟩ := exists_nat_ge (((C : ℝ) + 1) / ε)
  have hCk : (C : ℝ) + 1 ≤ ε * k := by
    rw [div_le_iff₀ hε0] at hk
    linarith
  have hkpos : 0 < k := by
    have : (0 : ℝ) < k := by nlinarith [Nat.cast_nonneg (α := ℝ) C]
    exact_mod_cast this
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hεk : 1 / (k : ℝ) ≤ ε := by
    rw [div_le_iff₀ hkR]
    nlinarith [Nat.cast_nonneg (α := ℝ) C]
  have hCfloor : C ≤ ⌊ε * k⌋₊ := Nat.le_floor (by linarith)
  obtain ⟨n, u, cover, hcover⟩ := hK k ε hkpos hεk hε1
  refine ⟨n, k, u, cover, fun S hS => ?_⟩
  have hS' : FeasibleTrajectory k ⌊ε * k⌋₊ S :=
    ⟨hS.1, hS.2.1, fun t => (hS.2.2 t).trans hCfloor⟩
  obtain ⟨t, A, hA, hAc, hpos, hle⟩ := hcover S hS'
  exact ⟨t, A, hA, hAc, by nlinarith⟩

end ConsistentSubmodular.GridStream
