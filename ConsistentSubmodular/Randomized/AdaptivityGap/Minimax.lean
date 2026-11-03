module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# Finite minimax duality (Lemma 5)

Lemma 5 of Appendix A.4: for a window with `κ ≥ 1` and `f(O_0) > 0`, the value `ρ⋆`
of the linear program (1) is
`max_{α ∈ Δ} min_j Σ_i α_i w_{i,j} = min_{β ∈ Δ} max_i Σ_j β_j w_{i,j}` for the
normalized payoffs `w_{i,j} = f(O_i ∪ R_j) / f(O_j ∪ R_j)`.

Finite minimax duality is proved for every square matrix `w` by its saddle point
(`saddlePoint`): a value `v` and distributions `a` and `b` on the indices with
`Σ_i a_i w_{i,j} ≥ v` for every column `j` and `Σ_j b_j w_{i,j} ≤ v` for every row
`i`. The distribution `a` maximizes the guarantee `min_j Σ_i a_i w_{i,j}` over the
compact simplex. If no `b` kept every row sum at most this maximum `v`, the
row-sum vectors of the distributions `b` would form a compact convex set
disjoint from the closed orthant `{y | y ≤ v}`. A separating functional then
has nonpositive coefficients, and its normalized negation is a distribution
that beats `v` in every column, contradicting the maximality of `v`.

Weak duality, `min_j Σ_i α_i w_{i,j} ≤ Σ_{i,j} α_i β_j w_{i,j} ≤ max_i Σ_j β_j w_{i,j}`,
then makes `v` both the largest guarantee and the smallest maximal row sum. For a
window the payoffs lie in `[0, 1]`, so `v` is also the value of the linear program.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Minimax

variable {m : ℕ}

/-- The guarantee `min_j Σ_i a_i w_{i,j}` of the maximizing distribution `a`. -/
def guarantee (w : Fin (m + 1) → Fin (m + 1) → ℝ) (a : Point m) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun j => ∑ i, a i * w i j

theorem guarantee_le (w : Fin (m + 1) → Fin (m + 1) → ℝ) (a : Point m) (j : Fin (m + 1)) :
    guarantee w a ≤ ∑ i, a i * w i j :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem continuous_guarantee (w : Fin (m + 1) → Fin (m + 1) → ℝ) :
    Continuous (guarantee w) := by
  unfold guarantee
  exact Continuous.finset_inf'_apply _ fun j _ => by fun_prop

/-- The row sums `(Σ_j b_j w_{i,j})_i` of a distribution `b`, as a linear map. -/
def rowSums (w : Fin (m + 1) → Fin (m + 1) → ℝ) : Point m →ₗ[ℝ] Point m where
  toFun b i := ∑ j, b j * w i j
  map_add' b c := by
    ext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r b := by
    ext i
    simp [Finset.mul_sum, mul_assoc]

/-- A continuous linear functional on `ℝ^{m+1}` is the pairing with its values on
the standard basis. -/
theorem functional_eq (f : Point m →L[ℝ] ℝ) (y : Point m) :
    f y = ∑ i, y i * f (Pi.single i 1) := by
  have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : Point m) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hy]
  simp [map_sum, map_smul]

/-- The separation step: if every distribution `b` has some row sum above `v`,
then some distribution `a` beats `v` in every column. -/
theorem exists_dominating (w : Fin (m + 1) → Fin (m + 1) → ℝ) (v : ℝ)
    (h : ∀ b : Point m, IsSimplex b → ∃ i, v < ∑ j, b j * w i j) :
    ∃ a : Point m, IsSimplex a ∧ ∀ j, v < ∑ i, a i * w i j := by
  classical
  let K : Set (Point m) := rowSums w '' stdSimplex ℝ (Fin (m + 1))
  let T : Set (Point m) := Set.Iic fun _ => v
  have hK : IsCompact K :=
    (isCompact_stdSimplex ℝ (Fin (m + 1))).image
      (LinearMap.continuous_of_finiteDimensional (rowSums w))
  have hKc : Convex ℝ K := (convex_stdSimplex ℝ (Fin (m + 1))).linear_image (rowSums w)
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro _ ⟨b, hb, rfl⟩ hbT
    obtain ⟨i, hi⟩ := h b hb
    exact absurd (hbT i) (not_le.mpr hi)
  obtain ⟨f, u, u', hfK, huu', hfT⟩ :=
    geometric_hahn_banach_compact_closed hKc hK (convex_Iic _) isClosed_Iic hdisj
  -- The coefficients `c_i = -f(e_i)` are nonnegative, because `f` is bounded
  -- below on the orthant `T`.
  let c : Point m := fun i => -f (Pi.single i 1)
  have hv : u' < f fun _ => v := hfT _ Set.self_mem_Iic
  have hc (i : Fin (m + 1)) : 0 ≤ c i := by
    by_contra hneg
    have hpos : 0 < f (Pi.single i 1) := by
      simp only [c] at hneg
      linarith
    let t := (f (fun _ => v) - u') / f (Pi.single i 1)
    have hmem : ((fun _ => v) - t • (Pi.single i (1 : ℝ) : Point m)) ∈ T := by
      intro j
      have ht : 0 ≤ t := div_nonneg (by linarith) hpos.le
      have hsingle : (0 : ℝ) ≤ (Pi.single i (1 : ℝ) : Point m) j := by
        rw [Pi.single_apply]
        split_ifs <;> norm_num
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith
    have hval := hfT _ hmem
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at hval
    linarith
  have hf (y : Point m) : f y = -∑ i, c i * y i := by
    rw [functional_eq f y]
    simp only [c, neg_mul, Finset.sum_neg_distrib, neg_neg]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- The coefficients are not all zero.
  have hS : 0 < ∑ i, c i := by
    rcases (Finset.sum_nonneg fun i _ => hc i).lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      have hzero : ∀ i, c i = 0 := by
        intro i
        exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).mp heq.symm i
          (Finset.mem_univ i)
      have hK0 := hfK _ ⟨_, single_mem_stdSimplex ℝ 0, rfl⟩
      rw [hf] at hK0 hv
      simp only [hzero, zero_mul, Finset.sum_const_zero, neg_zero] at hK0 hv
      linarith
  set S := ∑ i, c i with hSdef
  refine ⟨fun i => c i / S, ⟨fun i => div_nonneg (hc i) hS.le, ?_⟩, fun j => ?_⟩
  · rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  · -- The column `j` is the row-sum vector of the vertex `e_j`.
    have hcol : rowSums w (Pi.single j 1) = fun i => w i j := by
      ext i
      simp [rowSums, Pi.single_apply]
    have hKj := hfK _ ⟨_, single_mem_stdSimplex ℝ j, rfl⟩
    rw [hcol, hf] at hKj
    rw [hf] at hv
    have hvS : ∑ i, c i * v = v * S := by
      rw [hSdef, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hvS] at hv
    have hsum : v * S < ∑ i, c i * w i j := by linarith
    have heq : ∑ i, c i / S * w i j = (∑ i, c i * w i j) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    show v < ∑ i, c i / S * w i j
    rw [heq, lt_div_iff₀ hS]
    linarith

/-- Finite minimax duality for a square matrix `w`, stated by its saddle point: a
value `v`, a distribution `a` with `Σ_i a_i w_{i,j} ≥ v` for every `j`, and a
distribution `b` with `Σ_j b_j w_{i,j} ≤ v` for every `i`. -/
theorem saddlePoint (w : Fin (m + 1) → Fin (m + 1) → ℝ) : ∃ v : ℝ,
    (∃ a : Point m, IsSimplex a ∧ ∀ j, v ≤ ∑ i, a i * w i j) ∧
    (∃ b : Point m, IsSimplex b ∧ ∀ i, ∑ j, b j * w i j ≤ v) := by
  obtain ⟨a, ha, hmax⟩ := (isCompact_stdSimplex ℝ (Fin (m + 1))).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ 0⟩ (continuous_guarantee w).continuousOn
  refine ⟨guarantee w a, ⟨a, ha, guarantee_le w a⟩, ?_⟩
  by_contra hno
  push Not at hno
  obtain ⟨a', ha', hbeat⟩ := exists_dominating w (guarantee w a) hno
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    fun j => ∑ i, a' i * w i j
  have hlt : guarantee w a < guarantee w a' := by
    unfold guarantee at hbeat ⊢
    rw [hj]
    exact hbeat j
  exact absurd (isMaxOn_iff.mp hmax a' ha') (not_le.mpr hlt)

/-- The largest row sum `max_i Σ_j b_j w_{i,j}` against the distribution `b`. -/
def rowMax (w : Fin (m + 1) → Fin (m + 1) → ℝ) (b : Point m) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j, b j * w i j

/-- Weak duality: `min_j Σ_i a_i w_{i,j} ≤ Σ_j b_j Σ_i a_i w_{i,j} =
Σ_i a_i Σ_j b_j w_{i,j} ≤ max_i Σ_j b_j w_{i,j}`. -/
theorem guarantee_le_rowMax (w : Fin (m + 1) → Fin (m + 1) → ℝ) {a b : Point m}
    (ha : IsSimplex a) (hb : IsSimplex b) : guarantee w a ≤ rowMax w b := by
  calc guarantee w a = ∑ j, b j * guarantee w a := by rw [← Finset.sum_mul, hb.2, one_mul]
    _ ≤ ∑ j, b j * ∑ i, a i * w i j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (guarantee_le w a j) (hb.1 j)
    _ = ∑ i, a i * ∑ j, b j * w i j := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ i, a i * rowMax w b :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun i => ∑ j, b j * w i j) (Finset.mem_univ i)) (ha.1 i)
    _ = rowMax w b := by rw [← Finset.sum_mul, ha.2, one_mul]

/-! ### Lemma 5 for the normalized payoffs of a window -/

section Window

variable {n : ℕ} (W : WindowInstance n)

/-- The stage-`0` benchmark `f(O_0 ∪ R_0)` is `f(O_0)`. -/
theorem benchmark_zero : W.benchmark 0 = W.objective.value (W.candidate 0) := by
  simp [WindowInstance.benchmark, W.arrivals_zero]

/-- Optimality and monotonicity: `f(O_j ∪ R_j) ≥ f(O_0 ∪ R_j) ≥ f(O_0)`. -/
theorem benchmark_zero_le (j : Fin (W.lastStage + 1)) : W.benchmark 0 ≤ W.benchmark j := by
  have hopt := W.candidate_optimal j (W.candidate 0) (W.candidate_subset 0) (W.candidate_card 0)
  have hsub : W.candidate 0 ∪ W.arrivals 0 ⊆ W.candidate 0 ∪ W.arrivals j := by
    rw [W.arrivals_zero]
    exact Finset.union_subset_union (subset_refl _) (Finset.empty_subset _)
  have hmono := W.objective.monotone _ _ hsub
  unfold WindowInstance.benchmark
  linarith

/-- `Σ_i a_i w_{i,j} = Σ_i a_i f(O_i ∪ R_j) / f(O_j ∪ R_j)`. -/
theorem sum_mul_payoff (a : Point W.lastStage) (j : Fin (W.lastStage + 1)) :
    ∑ i, a i * W.payoff i j =
      (∑ i, a i * W.objective.value (W.candidate i ∪ W.arrivals j)) / W.benchmark j := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => (mul_div_assoc _ _ _).symm

/-- **Lemma 5** (finite minimax duality, Appendix A.4). With `f(O_0) > 0` every
benchmark is positive, and every payoff lies in `[0, 1]` by nonnegativity and the
optimality of `O_j` against `O_i`. The saddle value `v` of the payoffs is the
largest guarantee and the smallest maximal row sum by weak duality, and the feasible
values of the linear program (1) are exactly `[0, v]`, so `ρ⋆ = v`. -/
theorem minimax : MinimaxGoal := by
  intro n W _ h0
  have hpos : ∀ j, 0 < W.benchmark j := fun j =>
    lt_of_lt_of_le (by rw [benchmark_zero]; exact h0) (benchmark_zero_le W j)
  have hw0 : ∀ i j, 0 ≤ W.payoff i j := fun i j =>
    div_nonneg (W.objective.nonnegative _) (hpos j).le
  have hw1 : ∀ i j, W.payoff i j ≤ 1 := fun i j => by
    rw [WindowInstance.payoff, div_le_one (hpos j)]
    exact W.candidate_optimal j (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  obtain ⟨v, ⟨a, ha, hav⟩, ⟨b, hb, hbv⟩⟩ := saddlePoint W.payoff
  have hga : v ≤ guarantee W.payoff a := Finset.le_inf' _ _ fun j _ => hav j
  have hrb : rowMax W.payoff b ≤ v := Finset.sup'_le _ _ fun i _ => hbv i
  have hweak := guarantee_le_rowMax W.payoff ha hb
  -- A distribution `α` meets a level `ρ` of the linear program at every stage
  -- exactly when `ρ ≤ min_j Σ_i α_i w_{i,j}`.
  have hfeas : ∀ (α : Point W.lastStage) (ρ : ℝ), (∀ j, ρ * W.benchmark j ≤
      ∑ i, α i * W.objective.value (W.candidate i ∪ W.arrivals j)) ↔
        ρ ≤ guarantee W.payoff α := by
    intro α ρ
    unfold guarantee
    rw [Finset.le_inf'_iff]
    refine forall_congr' fun j => ?_
    rw [sum_mul_payoff, le_div_iff₀ (hpos j)]
    simp
  have hv0 : 0 ≤ v :=
    (Finset.sum_nonneg fun j _ => mul_nonneg (hb.1 j) (hw0 0 j)).trans (hbv 0)
  have hv1 : v ≤ 1 := by
    calc v ≤ ∑ i, a i * W.payoff i 0 := hav 0
      _ ≤ ∑ i, a i * 1 := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hw1 i 0) (ha.1 i)
      _ = 1 := by rw [← Finset.sum_mul, ha.2, one_mul]
  have hlp : W.lpValue = v := by
    apply IsGreatest.csSup_eq
    refine ⟨⟨hv0, hv1, a, ha, (hfeas a v).mpr hga⟩, ?_⟩
    rintro ρ ⟨-, -, α, hα, hρ⟩
    exact ((hfeas α ρ).mp hρ).trans ((guarantee_le_rowMax W.payoff hα hb).trans hrb)
  rw [hlp]
  refine ⟨⟨⟨a, ha, le_antisymm hga (hweak.trans hrb)⟩, ?_⟩,
    ⟨⟨b, hb, le_antisymm (hga.trans hweak) hrb⟩, ?_⟩⟩
  · rintro x ⟨α, hα, rfl⟩
    exact (guarantee_le_rowMax W.payoff hα hb).trans hrb
  · rintro x ⟨β, hβ, rfl⟩
    exact hga.trans (guarantee_le_rowMax W.payoff ha hβ)

end Window

end ConsistentSubmodular.Minimax
