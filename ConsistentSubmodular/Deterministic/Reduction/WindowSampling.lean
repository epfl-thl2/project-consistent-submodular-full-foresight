module

public import ConsistentSubmodular.Deterministic.Reduction.WindowSamples
public import ConsistentSubmodular.Deterministic.Reduction.WindowTransfer
public import ConsistentSubmodular.Deterministic.Reduction.ResidualRounding
public import ConsistentSubmodular.Deterministic.Reduction.PathSubdivision
public import ConsistentSubmodular.Deterministic.Reduction.PhysicalIntersection
public import ConsistentSubmodular.Deterministic.Reduction.RoundingBudget

@[expose] public section

/-! Simultaneous rounding of both local paths and all retained buffer tests. -/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ConsistentSubmodular
namespace FractionalWindow

variable {n κ N T S : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  (W : FractionalWindow f old Q hQ κ N T initial terminal α S)

theorem exists_windowSamples (hN : 200 ≤ N) (hS : 0 < S) (hκ : windowHeavyBound N S ≤ κ)
    (hV : 0 < f.bufferedOptimum old ∅ κ) :
    Nonempty (WindowSamples W (windowHeavyBound N S)) := by
  classical
  let V := f.bufferedOptimum old ∅ κ
  let B := windowTestBound N S
  let H := windowHeavyBound N S
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hSr : (0 : ℝ) < S := Nat.cast_pos.mpr hS
  have hBr : (0 : ℝ) < B := Nat.cast_pos.mpr (windowTestBound_pos N S)
  have hHpos : 0 < H := windowHeavyBound_pos S hNpos
  have hκpos : 0 < κ := window_scale_positive hNpos hκ
  have hκr : (0 : ℝ) < κ := Nat.cast_pos.mpr hκpos
  have hsubpos : 0 < 8 * N := by omega
  let E := W.entry.subdivide (8 * N)
  let X := W.exit.subdivide (8 * N)
  let P := CompatibleProfile.fromPhysical f W.cores Q hQ
  have hE : E.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q 0) κ ≤ P.multilinearValue 0 p) :=
    (show W.entry.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q 0) κ ≤
      P.multilinearValue 0 p) from W.entry_safe).subdivide (8 * N) hsubpos
  have hX : X.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q T) κ ≤ P.multilinearValue T p) :=
    (show W.exit.Along (fun p => IsSimplex p ∧ α * f.bufferedOptimum old (Q T) κ ≤
      P.multilinearValue T p) from W.exit_safe).subdivide (8 * N) hsubpos
  let Node := Fin (E.pieces + 1) ⊕ Fin (X.pieces + 1)
  let Edge := Fin E.pieces ⊕ Fin X.pieces
  let Test := Edge ⊕ Fin (3 * N + 2)
  let point : Node → Point (3 * N + 1) := Sum.elim E.node X.node
  let z := fun t => physicalProbability W.cores (point t)
  let edgeL : Edge → Node := Sum.elim (fun j => .inl j.castSucc) (fun j => .inr j.castSucc)
  let edgeR : Edge → Node := Sum.elim (fun j => .inl j.succ) (fun j => .inr j.succ)
  let cp : Node := .inl (Fin.last E.pieces)
  let left : Test → Node := Sum.elim edgeL (fun _ => cp)
  let right : Test → Node := Sum.elim edgeR (fun _ => cp)
  let buffers : Test → Finset (Fin n) := Sum.elim
    (Sum.elim (fun _ => Q 0) (fun _ => Q T)) (fun i => Q (W.retained i))
  let targets : Test → ℝ := Sum.elim
    (Sum.elim (fun _ => α * f.bufferedOptimum old (Q 0) κ - V / (4 * N))
      (fun _ => α * f.bufferedOptimum old (Q T) κ - V / (4 * N)))
    (fun i => α * f.bufferedOptimum old (Q (W.retained i)) κ)
  have hpoint (t : Node) : IsSimplex (point t) := by
    cases t with
    | inl j => exact (hE.1 j).1
    | inr j => exact (hX.1 j).1
  have hz (t : Node) (e) : 0 ≤ z t e ∧ z t e ≤ 1 :=
    physicalProbability_mem_unitInterval W.cores _ (hpoint t) e
  have hsupport (t : Node) (e) (he : e ∉ old) : z t e = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hn : e ∉ W.cores i := fun hi => he (W.core_subset i hi)
    simp [hn]
  have hmass (t : Node) : (∑ e, z t e) ≤ κ :=
    physicalProbability_total_le W.cores _ (hpoint t).1 (hpoint t).2.le W.core_card
  have hcp : point cp = W.checkpoint := by
    exact (W.entry.subdivide_terminal (8 * N) hsubpos).trans W.entry_terminal
  have hdist (γ : PolygonalPath (3 * N + 1)) (hcube : ∀ j, IsSimplex (γ.node j))
      (j : Fin (γ.subdivide (8 * N)).pieces) :
      typeL1 ((γ.subdivide (8 * N)).node j.castSucc) ((γ.subdivide (8 * N)).node j.succ) ≤ 1 / (4 * N) := by
    have h := γ.subdivide_step_le hcube (8 * N) hsubpos j
    have he : (2 : ℝ) / (8 * N : ℕ) = 1 / (4 * N) := by push_cast; ring
    rwa [he] at h
  have htarget (i : Test) : targets i ≤ finiteExpectation
      (fun e => min (z (left i) e) (z (right i) e)) (fun S => f.value (buffers i ∪ S)) := by
    cases i with
    | inl edge =>
      cases edge with
      | inl j =>
        have hlift := physical_intersection_lower f W.cores (Q 0) V hV.le W.core_value
          (E.node j.castSucc) (E.node j.succ) (hE.1 _).1 (hE.1 _).1
        have hd := mul_le_mul_of_nonneg_left (hdist W.entry (fun j => (W.entry_safe.1 j).1) j) hV.le
        have hv := (hE.1 j.castSucc).2
        change α * f.bufferedOptimum old (Q 0) κ - V / (4 * N) ≤ _
        change α * f.bufferedOptimum old (Q 0) κ ≤ finiteExpectation _ (f.onTypes W.cores (Q 0)).value at hv
        dsimp only [z, point, left, right, edgeL, edgeR, buffers, Sum.elim] at *
        change V * (∑ i, |E.node j.castSucc i - E.node j.succ i|) ≤ V * (1 / (4 * N)) at hd
        rw [mul_one_div] at hd
        nlinarith only [hlift, hd, hv]
      | inr j =>
        have hlift := physical_intersection_lower f W.cores (Q T) V hV.le W.core_value
          (X.node j.castSucc) (X.node j.succ) (hX.1 _).1 (hX.1 _).1
        have hd := mul_le_mul_of_nonneg_left (hdist W.exit (fun j => (W.exit_safe.1 j).1) j) hV.le
        have hv := (hX.1 j.castSucc).2
        change α * f.bufferedOptimum old (Q T) κ - V / (4 * N) ≤ _
        change α * f.bufferedOptimum old (Q T) κ ≤ finiteExpectation _ (f.onTypes W.cores (Q T)).value at hv
        dsimp only [z, point, left, right, edgeL, edgeR, buffers, Sum.elim] at *
        change V * (∑ i, |X.node j.castSucc i - X.node j.succ i|) ≤ V * (1 / (4 * N)) at hd
        rw [mul_one_div] at hd
        nlinarith only [hlift, hd, hv]
    | inr i =>
      simpa only [targets, left, right, buffers, Sum.elim, z, min_self, hcp] using W.retained_physical i
  have hpathcost (γ : PolygonalPath (3 * N + 1)) (hcube : ∀ j, IsSimplex (γ.node j)) :
      (∑ j : Fin (γ.subdivide (8 * N)).pieces,
        ∑ e, |physicalProbability W.cores ((γ.subdivide (8 * N)).node j.castSucc) e -
          physicalProbability W.cores ((γ.subdivide (8 * N)).node j.succ) e|) ≤
        2 * (γ.pieces : ℝ) * κ := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin (γ.subdivide (8 * N)).pieces) _ =>
      physicalProbability_l1_le W.cores ((γ.subdivide (8 * N)).node j.castSucc)
        ((γ.subdivide (8 * N)).node j.succ) W.core_card)
    rw [← Finset.mul_sum] at hsum
    have hh := mul_le_mul_of_nonneg_left (γ.subdivide_length_le hcube (8 * N) hsubpos) (Nat.cast_nonneg κ : (0 : ℝ) ≤ κ)
    change _ ≤ (κ : ℝ) * (γ.subdivide (8 * N)).length at hsum
    nlinarith only [hsum, hh]
  have hcostBudget : (∑ j : Edge, ∑ e, |z (edgeL j) e - z (edgeR j) e|) ≤
      (8 * (S : ℝ) * κ) * (1 / 4 : ℝ) := by
    rw [Fintype.sum_sum_type]
    have he := hpathcost W.entry (fun j => (W.entry_safe.1 j).1)
    have hx := hpathcost W.exit (fun j => (W.exit_safe.1 j).1)
    have hb := window_cost_budget S (W.entry.pieces + W.exit.pieces) κ W.pieces
    push_cast at hb
    dsimp only [z, point, edgeL, edgeR, Sum.elim]
    nlinarith only [he, hx, hb]
  have hcount : Fintype.card Node + Fintype.card Test ≤ B := by
    have hnodeCard : Fintype.card Node = (E.pieces + 1) + (X.pieces + 1) := by
      exact (Fintype.card_congr (show Node ≃ Fin ((E.pieces + 1) + (X.pieces + 1)) from
        finSumFinEquiv)).trans (Fintype.card_fin _)
    have htestCard : Fintype.card Test = (E.pieces + X.pieces) + (3 * N + 2) := by
      exact (Fintype.card_congr (show Test ≃ Fin ((E.pieces + X.pieces) + (3 * N + 2)) from
        (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans (Fintype.card_fin _)
    apply window_test_count N S (W.entry.pieces + W.exit.pieces) _ _ W.pieces
    · rw [hnodeCard]
      simp only [E, X, PolygonalPath.subdivide_pieces]
      nlinarith
    · rw [htestCard]
      simp only [E, X, PolygonalPath.subdivide_pieces]
      nlinarith
  have hcountNode : (Fintype.card Node : ℝ) ≤ B := by exact_mod_cast (show Fintype.card Node ≤ B by omega)
  have hcountTest : (Fintype.card Test : ℝ) ≤ B := by exact_mod_cast (show Fintype.card Test ≤ B by omega)
  obtain ⟨c, hcdef⟩ : ∃ c, c = logBudget (4 * B) := ⟨_, rfl⟩
  have hc : 4 * B ≤ 2 ^ c := hcdef ▸ (lt_two_pow_logBudget _).le
  have hHeq : H = 64 * N ^ 2 * c := by rw [hcdef]; rfl
  have hHc : 64 * N ^ 2 * c ≤ H := hHeq.ge
  have hlarge : 4 * (N : ℝ) ^ 2 * c ≤ κ := by
    have hHκ : H ≤ κ := hκ
    have h4 : 4 * N ^ 2 * c ≤ H := by
      rw [hHeq]
      exact Nat.mul_le_mul_right c (Nat.mul_le_mul_right (N ^ 2) (by norm_num))
    exact_mod_cast h4.trans hHκ
  have hb2 : (κ : ℝ) / N ≤ 2 * κ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    have := div_le_self hκr.le hN1
    linarith
  obtain ⟨D, S, hDU, hDH, hSU, hzero, hone, hcard, hval, hcost, hequal⟩ :=
    f.exists_residual_rounding old κ H hHpos hκ V hV
      (fun A hA hAk => by simpa using f.le_bufferedOptimum (Q := ∅) hA hAk)
      z hz hsupport hmass buffers left right edgeL edgeR targets htarget
      (V / (4 * N)) ((κ : ℝ) / N) (8 * (S : ℝ) * κ) (1 / (4 * B)) (1 / (4 * B)) (1 / 4)
      (by positivity) (by positivity) hb2 (mul_pos (mul_pos (by norm_num) hSr) hκr)
      (RoundingBudget.size_budget_exp B N c κ (windowTestBound_pos N S) hNpos hc hlarge hκr)
      (RoundingBudget.window_value_budget_exp B N c H V (windowTestBound_pos N S) hNpos hV
        hHpos hc hHc)
      hcostBudget (RoundingBudget.union_budget B _ _ hBr hcountNode hcountTest)
  have hpure (t : Node) (A : Finset (Fin n))
      (ht : ∀ e, z t e = if e ∈ A then 1 else 0) : S t = A := by
    ext e
    by_cases he : e ∈ A
    · exact ⟨fun _ => he, fun _ => hone t e (by simp [ht, he])⟩
    · exact ⟨fun hs => (hzero t e (by simp [ht, he]) hs).elim, fun h => (he h).elim⟩
  have hE0 : S (.inl 0) = initial := by
    apply hpure
    intro e
    change physicalProbability W.cores (E.node 0) e = _
    rw [show E.node 0 = vertex 0 from (W.entry.subdivide_initial (8 * N) hsubpos).trans W.entry_initial,
      physicalProbability_vertex, W.core_initial]
  have hXT : S (.inr (Fin.last X.pieces)) = terminal := by
    apply hpure
    intro e
    change physicalProbability W.cores (X.node (Fin.last X.pieces)) e = _
    rw [show X.node (Fin.last X.pieces) = vertex (Fin.last (3 * N + 1)) from
      (W.exit.subdivide_terminal (8 * N) hsubpos).trans W.exit_terminal,
      physicalProbability_vertex, W.core_terminal]
  have hjoin : S cp = S (.inr 0) := by
    apply hequal
    intro e
    change physicalProbability W.cores (point cp) e = physicalProbability W.cores (X.node 0) e
    rw [hcp, show X.node 0 = W.checkpoint from (W.exit.subdivide_initial (8 * N) hsubpos).trans W.exit_initial]
  have hVle (t : ℕ) : V ≤ f.bufferedOptimum old (Q t) κ := by
    exact f.bufferedOptimum_mono (Finset.empty_subset (Q t))
  have hsmall : V / (4 * N) ≤ V / N := by
    have h : (0 : ℝ) ≤ V / N := div_nonneg hV.le hNr.le
    have he : V / (4 * N) = (V / N) / 4 := by ring
    rw [he]
    linarith
  have htest (i : Fin (3 * N + 2)) : α * f.bufferedOptimum old (Q (W.retained i)) κ - V / N ≤
      f.value (Q (W.retained i) ∪ (D ∪ S cp)) := by
    have h := hval (.inr i)
    simp only [targets, buffers, left, right, Sum.elim, Finset.inter_self] at h
    linarith only [h, hsmall]
  have hrelax (t : ℕ) : (α - 2 / N) * f.bufferedOptimum old (Q t) κ ≤
      α * f.bufferedOptimum old (Q t) κ - V / (4 * N) - V / (4 * N) := by
    have hm := div_le_div_of_nonneg_right (hVle t) hNr.le
    have he : V / (4 * N) = (V / N) / 4 := by ring
    have hf : (0 : ℝ) ≤ f.bufferedOptimum old (Q t) κ / N :=
      div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr.le
    rw [he]
    have he2 : (2 / N) * f.bufferedOptimum old (Q t) κ = 2 * (f.bufferedOptimum old (Q t) κ / N) := by ring
    nlinarith only [hm, hf, he2]
  refine ⟨{
    forced := D
    forced_subset := hDU
    forced_card := hDH
    entryPieces := E.pieces
    exitPieces := X.pieces
    entry := fun j => S (.inl j)
    exit := fun j => S (.inr j)
    entry_initial := hE0
    join := hjoin
    exit_terminal := hXT
    entry_subset := fun j => hSU (.inl j)
    exit_subset := fun j => hSU (.inr j)
    entry_card := fun j => hcard (.inl j)
    exit_card := fun j => hcard (.inr j)
    cost := ?_
    entry_first_good := ?_
    exit_first_good := ?_
    entry_intersection := ?_
    exit_intersection := ?_
    checkpoint_tests := htest
  }⟩
  · rw [Fintype.sum_sum_type] at hcost
    simpa only [edgeL, edgeR, Sum.elim, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hcost.le
  · have ht := htest 0
    rw [W.retained_initial] at ht
    have hm := f.monotone _ _ (show Q 0 ∪ initial ⊆ Q 0 ∪ (D ∪ S (.inl 0)) by
      rw [hE0]; intro e he; simp only [Finset.mem_union] at he ⊢; tauto)
    have hopt := W.retained_optimal 0
    rw [W.retained_initial, W.core_initial] at hopt
    rw [hopt] at hm
    have hnonneg := f.bufferedOptimum_nonnegative old (Q 0) κ
    have hcoef : α - 2 / N ≤ 1 := by
      have : (0 : ℝ) ≤ 2 / N := by positivity
      linarith [W.level_le]
    exact (mul_le_of_le_one_left hnonneg hcoef).trans hm
  · have ht := htest (Fin.last (3 * N + 1))
    rw [W.retained_terminal, hjoin] at ht
    have hm := div_le_div_of_nonneg_right (hVle T) hNr.le
    have hf : (0 : ℝ) ≤ f.bufferedOptimum old (Q T) κ / N :=
      div_nonneg (f.bufferedOptimum_nonnegative _ _ _) hNr.le
    have he : (2 / N) * f.bufferedOptimum old (Q T) κ = 2 * (f.bufferedOptimum old (Q T) κ / N) := by ring
    nlinarith only [ht, hm, hf, he]
  · intro j
    exact (hrelax 0).trans (hval (.inl (.inl j)))
  · intro j
    exact (hrelax T).trans (hval (.inl (.inr j)))

end FractionalWindow
end ConsistentSubmodular
