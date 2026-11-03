module

public import ConsistentSubmodular.Randomized.AdaptivityGap.Minimax

@[expose] public section

/-!
# From interval selection to addition robustness (Lemma 2)

The proof of Lemma 2 in Appendix A.4. If `κ = 0`, or if `κ ≥ 1` and `f(O_0) = 0`,
the candidate `O_0` already achieves every benchmark. Otherwise candidate `i` of a
window gives the interval `[ℓ_i, r_i] = [f(R_i), f(O_i ∪ R_i)]`, and claim (4) bounds
`f(O_i ∪ R_j)` from below by the interval value `v(i, j)`. For every distribution
`β` of the adversary on the stages, the reweighted distribution
`p_j = (β_j / r_j) / Z` turns an adaptivity gap of at least `α` into a row of the
normalized payoff matrix `w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)` worth at least `α`
against `β`. Lemma 5 then gives `ρ⋆ ≥ α`, and its maximizing distribution over the
candidates is `α`-addition robust.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.IntervalSelection

/-! ### Interval values -/

section Intervals

variable {N : ℕ} (I : IntervalInstance N)

/-- An interval is worth its right endpoint at its own realization. -/
theorem value_self (j : Fin (N + 1)) : I.value j j = I.right j := by
  unfold IntervalInstance.value
  rw [max_self, max_eq_right (sub_nonneg.mpr (I.left_le_right j))]
  ring

end Intervals

/-! ### Two properties of the objective -/

section Objective

variable {n : ℕ} (f : Objective n)

/-- Diminishing returns for nested sets `A ⊆ B`:
`f(X ∪ B) - f(B) ≤ f(X ∪ A) - f(A)`. -/
theorem diminishing {A B : Finset (Fin n)} (hAB : A ⊆ B) (X : Finset (Fin n)) :
    f.value (X ∪ B) + f.value A ≤ f.value (X ∪ A) + f.value B := by
  have h := f.submodular (X ∪ A) B
  have hunion : X ∪ A ∪ B = X ∪ B := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr hAB]
  have hinter : A ⊆ (X ∪ A) ∩ B := fun e he =>
    Finset.mem_inter.mpr ⟨Finset.mem_union_right X he, hAB he⟩
  have hmono := f.monotone A ((X ∪ A) ∩ B) hinter
  rw [hunion] at h
  linarith

/-- Elements whose singletons are worth no more than the empty set add nothing. -/
theorem value_union_le (A X : Finset (Fin n)) (h : ∀ e ∈ A, f.value {e} ≤ f.value ∅) :
    f.value (A ∪ X) ≤ f.value X := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert e A he ih =>
    have hsub := f.submodular {e} (A ∪ X)
    have hmono := f.monotone ∅ ({e} ∩ (A ∪ X)) (Finset.empty_subset _)
    have heq : insert e A ∪ X = {e} ∪ (A ∪ X) := by
      rw [Finset.insert_eq, Finset.union_assoc]
    have he' := h e (Finset.mem_insert_self e A)
    have ih' := ih fun e' he' => h e' (Finset.mem_insert_of_mem he')
    rw [heq]
    linarith

end Objective

/-! ### The intervals of a window -/

section Window

variable {n : ℕ} (W : WindowInstance n)

/-- The interval instance in the proof of Lemma 2: candidate `i` gives the
interval `[f(R_i), f(O_i ∪ R_i)]`, and `p` is a distribution on the stages. -/
def windowIntervals (p : Point W.lastStage) (hp : IsSimplex p) : IntervalInstance W.lastStage where
  left i := W.objective.value (W.arrivals i)
  right i := W.benchmark i
  prob := p
  left_nonneg _ := W.objective.nonnegative _
  left_le_right _ := W.objective.monotone _ _ Finset.subset_union_right
  prob_nonneg := hp.1
  prob_sum := hp.2

/-- Claim (4): `f(O_i ∪ R_j) ≥ v(i, j)`. For `j ≤ i` this is diminishing returns,
and for `j ≥ i` it is monotonicity. -/
theorem value_le_objective (p : Point W.lastStage) (hp : IsSimplex p)
    (i j : Fin (W.lastStage + 1)) :
    (windowIntervals W p hp).value i j ≤ W.objective.value (W.candidate i ∪ W.arrivals j) := by
  simp only [IntervalInstance.value, windowIntervals, WindowInstance.benchmark]
  rcases le_total j i with hji | hij
  · have hR := W.arrivals_mono hji
    have hl := W.objective.monotone _ _ hR
    have hd := diminishing W.objective hR (W.candidate i)
    have hr := W.objective.monotone (W.arrivals i) (W.candidate i ∪ W.arrivals i)
      Finset.subset_union_right
    rw [max_eq_left hl, max_eq_right (sub_nonneg.mpr hr)]
    linarith
  · have hR := W.arrivals_mono hij
    have hl := W.objective.monotone _ _ hR
    have h1 := W.objective.monotone (W.arrivals j) (W.candidate i ∪ W.arrivals j)
      Finset.subset_union_right
    have h2 := W.objective.monotone (W.candidate i ∪ W.arrivals i)
      (W.candidate i ∪ W.arrivals j) (Finset.union_subset_union_right hR)
    rw [max_eq_right hl]
    rcases le_total 0 (W.objective.value (W.candidate i ∪ W.arrivals i) -
        W.objective.value (W.arrivals j)) with h | h
    · rw [max_eq_right h]
      linarith
    · rw [max_eq_left h]
      linarith

/-- If `f(O_0) = 0`, then the singletons of every candidate are worth no more than
`∅`, so no candidate adds value to the arrivals: `f(O_j ∪ R_j) ≤ f(R_j)`. This is
the degenerate case that precedes the normalized form of the linear program (1). -/
theorem benchmark_le_of_zero (h0 : W.benchmark 0 ≤ 0) (j : Fin (W.lastStage + 1)) :
    W.benchmark j ≤ W.objective.value (W.arrivals j) := by
  have hO0 : W.objective.value (W.candidate 0) ≤ 0 := by
    simpa [WindowInstance.benchmark, W.arrivals_zero] using h0
  have hsingle : ∀ e ∈ W.candidate j, W.objective.value {e} ≤ W.objective.value ∅ := by
    intro e he
    have hcard : ({e} : Finset (Fin n)).card ≤ W.coreBudget := by
      rw [Finset.card_singleton]
      exact (Finset.card_pos.mpr ⟨e, he⟩).trans_le (W.candidate_card j)
    have hopt := W.candidate_optimal 0 {e}
      (Finset.singleton_subset_iff.mpr (W.candidate_subset j he)) hcard
    rw [W.arrivals_zero, Finset.union_empty, Finset.union_empty] at hopt
    have := W.objective.nonnegative ∅
    linarith
  exact value_union_le W.objective _ _ hsingle

theorem isSimplex_vertex (i : Fin (W.lastStage + 1)) : IsSimplex (vertex i) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold vertex
    split_ifs <;> norm_num
  · simp [vertex]

/-- The degenerate case `κ ≥ 1` and `f(O_0) = 0`: every distribution over the
candidates is `α`-addition robust for `α ≤ 1`, for example the vertex `δ_0`. -/
theorem candidates_of_degenerate {α : ℝ} (hα1 : α ≤ 1) (h0 : W.benchmark 0 ≤ 0) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  refine ⟨vertex 0, isSimplex_vertex W 0, fun j => ?_⟩
  have hsum : ∑ i, vertex 0 i * W.objective.value (W.candidate i ∪ W.arrivals j) =
      W.objective.value (W.candidate 0 ∪ W.arrivals j) := by
    simp [vertex]
  rw [hsum]
  have h1 := benchmark_le_of_zero W h0 j
  have h2 := W.objective.monotone (W.arrivals j) (W.candidate 0 ∪ W.arrivals j)
    Finset.subset_union_right
  have h3 := mul_le_of_le_one_left (W.objective.nonnegative (W.candidate j ∪ W.arrivals j)) hα1
  unfold WindowInstance.benchmark at h1 h3 ⊢
  linarith

/-- The degenerate case `κ = 0`: every candidate is empty, so returning
`O_0 = ∅` achieves the benchmark `f(R_j)` exactly. -/
theorem candidates_of_budget_zero {α : ℝ} (hα1 : α ≤ 1) (hκ : W.coreBudget = 0) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  have hempty : ∀ i, W.candidate i = ∅ := fun i =>
    Finset.card_eq_zero.mp (Nat.le_zero.mp (hκ ▸ W.candidate_card i))
  refine ⟨vertex 0, isSimplex_vertex W 0, fun j => ?_⟩
  have hsum : ∑ i, vertex 0 i * W.objective.value (W.candidate i ∪ W.arrivals j) =
      W.objective.value (W.candidate 0 ∪ W.arrivals j) := by
    simp [vertex]
  rw [hsum]
  unfold WindowInstance.benchmark
  rw [hempty j, hempty 0]
  exact mul_le_of_le_one_left (W.objective.nonnegative _) hα1

/-- The step of the proof of Lemma 2 for one distribution `β` of the adversary:
the reweighted distribution `p_j = (β_j / r_j) / Z` turns an adaptivity gap of at
least `α` into a row of the payoffs worth at least `α` against `β`,
`max_i Σ_j β_j w_{i,j} ≥ α`. -/
theorem le_rowMax_payoff {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hpos : ∀ j, 0 < W.benchmark j) (β : Point W.lastStage) (hβ : IsSimplex β) :
    α ≤ Minimax.rowMax W.payoff β := by
  classical
  let F : Fin (W.lastStage + 1) → Fin (W.lastStage + 1) → ℝ :=
    fun i j => W.objective.value (W.candidate i ∪ W.arrivals j)
  -- Reweight the adversary's distribution `β` by the benchmarks `r_j`.
  have hterm (j : Fin (W.lastStage + 1)) : 0 ≤ β j / W.benchmark j :=
    div_nonneg (hβ.1 j) (hpos j).le
  set Z := ∑ j, β j / W.benchmark j with hZ
  have hZpos : 0 < Z := by
    rcases (Finset.sum_nonneg fun j _ => hterm j).lt_or_eq with h | h
    · exact h
    · exfalso
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp h.symm
      have hβ0 : ∑ j, β j = 0 := Finset.sum_eq_zero fun j hj => by
        have hj' := hzero j hj
        rwa [div_eq_zero_iff, or_iff_left (hpos j).ne'] at hj'
      rw [hβ.2] at hβ0
      norm_num at hβ0
  let p : Point W.lastStage := fun j => β j / W.benchmark j / Z
  have hp : IsSimplex p := ⟨fun j => div_nonneg (hterm j) hZpos.le, by
    simp only [p]
    rw [← Finset.sum_div, ← hZ, div_self hZpos.ne']⟩
  let I := windowIntervals W p hp
  -- The value in hindsight is at least `E_p[v(j, j)] = E_p[r_j] = 1 / Z`.
  have hadapt : 1 / Z ≤ I.adaptiveValue := by
    have hEr : ∑ j, p j * W.benchmark j = 1 / Z := by
      have hj (j : Fin (W.lastStage + 1)) : p j * W.benchmark j = β j / Z := by
        simp only [p]
        field_simp [(hpos j).ne', hZpos.ne']
      simp only [hj]
      rw [← Finset.sum_div, hβ.2]
    rw [← hEr]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hp.1 j)
    have hself := value_self I j
    have hle := Finset.le_sup' (fun i => I.value i j) (Finset.mem_univ j)
    simp only at hle
    rw [hself] at hle
    exact hle
  have hadaptPos : 0 < I.adaptiveValue := lt_of_lt_of_le (by positivity) hadapt
  -- The gap hypothesis: `α · E_p[max_h v(h, j)] ≤ max_i E_p[v(i, j)]`.
  have hfix : α * I.adaptiveValue ≤ I.fixedValue := by
    have hgapI := hgap _ I
    unfold IntervalInstance.adaptivityGap at hgapI
    rw [if_neg hadaptPos.ne', le_div_iff₀ hadaptPos] at hgapI
    exact hgapI
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    fun i => ∑ j, I.prob j * I.value i j
  -- The row of the best fixed interval is worth at least `α` against `β`.
  have hrow : α ≤ ∑ j, β j * W.payoff i j := by
    have hscale : ∑ j, β j * W.payoff i j = Z * ∑ j, p j * F i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [WindowInstance.payoff, p, F]
      field_simp [(hpos j).ne', hZpos.ne']
    rw [hscale]
    calc α = Z * (α * (1 / Z)) := by field_simp
      _ ≤ Z * (α * I.adaptiveValue) := by gcongr
      _ ≤ Z * I.fixedValue := by gcongr
      _ = Z * ∑ j, p j * I.value i j := by rw [IntervalInstance.fixedValue, hi]; rfl
      _ ≤ Z * ∑ j, p j * F i j := by
        gcongr with j
        · exact hp.1 j
        · exact value_le_objective W p hp i j
  exact hrow.trans (Finset.le_sup' (fun i => ∑ j, β j * W.payoff i j) (Finset.mem_univ i))

/-- The main case of Lemma 2, with `κ ≥ 1` and `f(O_0) > 0`: every distribution `β`
of the adversary meets a row worth at least `α`, so Lemma 5 gives `ρ⋆ ≥ α`, and the
distribution of Lemma 5 that attains `ρ⋆ = max_α min_j Σ_i α_i w_{i,j}` is
`α`-addition robust. -/
theorem candidates_of_gap_pos {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hκ : 1 ≤ W.coreBudget) (h0 : 0 < W.objective.value (W.candidate 0)) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  have hpos : ∀ j, 0 < W.benchmark j := fun j =>
    lt_of_lt_of_le (by rw [Minimax.benchmark_zero]; exact h0) (Minimax.benchmark_zero_le W j)
  obtain ⟨⟨⟨a, ha, haρ⟩, -⟩, ⟨⟨b, hb, hbρ⟩, -⟩⟩ := Minimax.minimax n W hκ h0
  -- `ρ⋆ = min_β max_i Σ_j β_j w_{i,j} ≥ α`.
  have hρ : α ≤ W.lpValue := by
    rw [hbρ]
    exact le_rowMax_payoff W hα0 hgap hpos b hb
  refine ⟨a, ha, fun j => ?_⟩
  -- `ρ⋆ = min_j Σ_i a_i w_{i,j} ≤ Σ_i a_i w_{i,j}`.
  have hcol : W.lpValue ≤ ∑ i, a i * W.payoff i j := by
    rw [haρ]
    exact Finset.inf'_le _ (Finset.mem_univ j)
  rw [Minimax.sum_mul_payoff, le_div_iff₀ (hpos j)] at hcol
  exact (mul_le_mul_of_nonneg_right hρ (hpos j).le).trans hcol

end Window

/-- **Lemma 2**, with a distribution over the candidates `O_0, ..., O_m`. -/
theorem candidates_of_gap {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap) {n : ℕ}
    (W : WindowInstance n) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by
  rcases Nat.eq_zero_or_pos W.coreBudget with hκ | hκ
  · exact candidates_of_budget_zero W hα1 hκ
  by_cases h0 : W.objective.value (W.candidate 0) ≤ 0
  · exact candidates_of_degenerate W hα1 (by rw [Minimax.benchmark_zero]; exact h0)
  · push Not at h0
    exact candidates_of_gap_pos W hα0 hgap hκ h0

/-- A distribution over the candidates is a distribution over sets of at most
`κ` present elements: push it forward along `i ↦ O_i`. -/
theorem isAdditionRobust_of_candidates {α : ℝ} {n : ℕ} {W : WindowInstance n}
    {p : Point W.lastStage} (hp : IsSimplex p)
    (h : ∀ j, α * W.benchmark j ≤
      ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j)) :
    ∃ w, W.IsAdditionRobust α w := by
  classical
  refine ⟨fun S => ∑ i, if W.candidate i = S then p i else 0, fun S => ?_, ?_, fun S hS => ?_,
    fun j => ?_⟩
  · exact Finset.sum_nonneg fun i _ => by
      split_ifs
      · exact hp.1 i
      · exact le_rfl
  · rw [Finset.sum_comm]
    simp [hp.2]
  · obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have hiS : W.candidate i = S := by
      by_contra hne
      simp [hne] at hi
    subst hiS
    exact ⟨W.candidate_subset i, W.candidate_card i⟩
  · refine (h j).trans_eq ?_
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [ite_mul]

/-- **Lemma 2** (from interval selection to addition robustness). -/
theorem intervalSelectionReduction : IntervalSelectionReductionGoal := by
  intro α hα0 hα1 hgap n W
  obtain ⟨p, hp, h⟩ := candidates_of_gap hα0 hα1 hgap W
  exact isAdditionRobust_of_candidates hp h

end ConsistentSubmodular.IntervalSelection
