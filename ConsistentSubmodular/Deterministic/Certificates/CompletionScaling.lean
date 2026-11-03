module

public import ConsistentSubmodular.Deterministic.Certificates.CompletionReduction
public import ConsistentSubmodular.Deterministic.Certificates.SafePaths

@[expose] public section

/-! Positive-scale normalization and the zero-scale compatible-profile case. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

namespace Objective

variable {d : ℕ} (f : Objective d)

def divided (c : ℝ) (hc : 0 < c) : Objective d where
  value I := f.value I / c
  nonnegative I := div_nonneg (f.nonnegative I) hc.le
  monotone I J h := (div_le_div_iff_of_pos_right hc).mpr (f.monotone I J h)
  submodular I J := by
    rw [← add_div, ← add_div]
    exact (div_le_div_iff_of_pos_right hc).mpr (f.submodular I J)

theorem residual_le_sum_singletons (I : Finset (Fin d)) :
    f.value I - f.value ∅ ≤ ∑ i ∈ I, (f.value {i} - f.value ∅) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.sum_insert ha]
    have hs := f.submodular I {a}
    have hd : Disjoint I {a} := Finset.disjoint_singleton_right.mpr ha
    rw [Finset.union_singleton, Finset.disjoint_iff_inter_eq_empty.mp hd] at hs
    linarith

theorem value_eq_empty_of_singletons (h : ∀ i, f.value {i} - f.value ∅ = 0)
    (I : Finset (Fin d)) : f.value I = f.value ∅ := by
  have hu := f.residual_le_sum_singletons I
  simp only [h, Finset.sum_const_zero] at hu
  have hl := f.monotone ∅ I (Finset.empty_subset _)
  linarith

end Objective

namespace CompatibleProfile

variable {d : ℕ} (P : CompatibleProfile d)

def divided (c : ℝ) (hc : 0 < c) : CompatibleProfile d where
  objective t := (P.objective t).divided c hc
  values_increase s t hst I := (div_le_div_iff_of_pos_right hc).mpr (P.values_increase s t hst I)
  marginals_decrease s t hst I J hIJ := by
    change (P.objective t).value J / c - (P.objective t).value I / c ≤
      (P.objective s).value J / c - (P.objective s).value I / c
    rw [← sub_div, ← sub_div]
    exact (div_le_div_iff_of_pos_right hc).mpr (P.marginals_decrease s t hst I J hIJ)

theorem divided_residual (c : ℝ) (hc : 0 < c) (t : ℕ) (i : Fin d) :
    (P.divided c hc).residual t i = P.residual t i / c := by
  exact (sub_div _ _ _).symm

variable {m : ℕ} (Q : CompatibleProfile (m + 1))

theorem divided_multilinearValue (c : ℝ) (hc : 0 < c) (t : ℕ) (p : Point m) :
    (Q.divided c hc).multilinearValue t p = Q.multilinearValue t p / c := by
  unfold multilinearValue finiteExpectation divided Objective.divided
  simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]

theorem divided_path_transfer (c : ℝ) (hc : 0 < c) (t : ℕ) (a : ℝ) (γ : PolygonalPath m)
    (h : (Q.divided c hc).SafePath t (a / c) γ) : Q.SafePath t a γ := by
  constructor
  · intro j
    have hj := h.1 j
    rw [Q.divided_multilinearValue] at hj
    exact ⟨hj.1, (div_le_div_iff_of_pos_right hc).mp hj.2⟩
  · intro j x hx hx'
    have hj := h.2 j x hx hx'
    rw [Q.divided_multilinearValue] at hj
    exact ⟨hj.1, (div_le_div_iff_of_pos_right hc).mp hj.2⟩

theorem checkpoint_positive_scale_of_finite_checkpoint
    (hfinite : FiniteCheckpointGoal) (hscale : 0 < Q.residual 0 0)
    (hopt : ∀ t : Fin (m + 1), ∀ i, Q.residual t.val i ≤ Q.residual t.val t) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  let c := Q.residual 0 0
  have hinit : (Q.divided c hscale).residual 0 0 = 1 := by
    rw [Q.divided_residual]
    exact div_self (ne_of_gt hscale)
  have hopt' : ∀ t : Fin (m + 1), ∀ i,
      (Q.divided c hscale).residual t.val i ≤ (Q.divided c hscale).residual t.val t := by
    intro t i
    rw [Q.divided_residual, Q.divided_residual]
    exact (div_le_div_iff_of_pos_right hscale).mpr (hopt t i)
  obtain ⟨p, entry, exit, hp, hsupp, hstage, he0, he1, hx0, hx1, hentry, hexit, hpieces⟩ :=
    (Q.divided c hscale).checkpoint_of_finite_checkpoint hinit hopt' hfinite
  refine ⟨p, entry, exit, hp, hsupp, ?_, he0, he1, hx0, hx1, ?_, ?_, hpieces⟩
  · intro t
    have ht := hstage t
    rw [Q.divided_multilinearValue] at ht
    change (3 : ℝ) / 4 * ((Q.objective t.val).value {t} / c) ≤ Q.multilinearValue t.val p / c at ht
    rw [← mul_div_assoc] at ht
    exact (div_le_div_iff_of_pos_right hscale).mp ht
  · apply Q.divided_path_transfer c hscale
    simpa only [divided, Objective.divided, mul_div_assoc] using hentry
  · apply Q.divided_path_transfer c hscale
    simpa only [divided, Objective.divided, mul_div_assoc] using hexit

theorem constant_of_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) (t : ℕ) (I : Finset (Fin (m + 1))) :
    (Q.objective t).value I = Q.baseline t := by
  apply (Q.objective t).value_eq_empty_of_singletons
  intro i
  have hu := (Q.residualOn_antitone (Nat.zero_le t) {i}).trans (hopt0 i)
  have hl := Q.residualOn_nonnegative t {i}
  rw [hzero] at hu
  exact le_antisymm hu hl

theorem multilinearValue_eq_baseline_of_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) (t : ℕ) (p : Point m) :
    Q.multilinearValue t p = Q.baseline t := by
  unfold multilinearValue
  have hfun : (Q.objective t).value = fun _ => Q.baseline t :=
    funext (Q.constant_of_zero_scale hzero hopt0 t)
  rw [hfun, finiteExpectation_const]

/-- Zero scale has a common exact checkpoint and one direct exit; no
normalization, atomization, or finite checkpoint assumption is used. -/
theorem checkpoint_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  have hval (t : ℕ) (i : Fin (m + 1)) (p : Point m) :
      (3 : ℝ) / 4 * (Q.objective t).value {i} ≤ Q.multilinearValue t p := by
    rw [Q.constant_of_zero_scale hzero hopt0, Q.multilinearValue_eq_baseline_of_zero_scale hzero hopt0]
    exact mul_le_of_le_one_left ((Q.objective t).nonnegative ∅) (by norm_num)
  refine ⟨vertex 0, PolygonalPath.constant (vertex 0),
    PolygonalPath.segment (vertex 0) (vertex (Fin.last m)), simplex_vertex 0,
    (by rw [supportCard_vertex]; omega), (fun t => hval t.val t _), rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · exact PolygonalPath.segment_terminal _ _
  · constructor
    · intro j
      exact ⟨simplex_vertex 0, hval 0 0 _⟩
    · intro j
      exact Fin.elim0 j
  · constructor
    · intro j
      constructor
      · change IsSimplex (if j = 0 then vertex 0 else vertex (Fin.last m))
        split_ifs <;> exact simplex_vertex _
      · exact hval m (Fin.last m) _
    · intro j x hx hx'
      change Fin 1 at j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      exact ⟨(simplex_vertex 0).mix (simplex_vertex (Fin.last m)) hx hx', hval m (Fin.last m) _⟩
  · simp

/-- Full compatible-profile reduction, including zero initial scale and
arbitrary nonnegative initial baseline. -/
theorem checkpoint_for_compatible (hfinite : FiniteCheckpointGoal)
    (hopt : ∀ t : Fin (m + 1), ∀ i, Q.residual t.val i ≤ Q.residual t.val t) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by
  by_cases hzero : Q.residual 0 0 = 0
  · exact Q.checkpoint_zero_scale hzero (hopt 0)
  · have hpos : 0 < Q.residual 0 0 :=
      lt_of_le_of_ne (Q.residualOn_nonnegative 0 {0}) (Ne.symm hzero)
    exact Q.checkpoint_positive_scale_of_finite_checkpoint hfinite hpos hopt

end CompatibleProfile

end ConsistentSubmodular
