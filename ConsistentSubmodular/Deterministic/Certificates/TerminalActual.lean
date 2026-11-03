module

public import ConsistentSubmodular.Deterministic.Certificates.SafePaths
public import ConsistentSubmodular.Deterministic.Certificates.TerminalPairGeometry

@[expose] public section

/-! Actual-coverage exits through a pure vertex. The pair may have arbitrary
overlap; its selected partner need not be the terminal type. -/

noncomputable section

namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem terminal_vertex_exit (b : Fin (m + 1))
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤ P.value (Fin.last m) (vertex b))
    (hno : ¬ (P.residual b (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual b (Fin.last m))) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = vertex b ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 1 := by
  by_cases hb : b = Fin.last m
  · subst b
    refine ⟨PolygonalPath.constant (vertex (Fin.last m)), rfl, rfl, ?_, by simp⟩
    exact (safePath_constant_iff _ _ _ _).2 ⟨simplex_vertex _, hgood⟩
  · refine ⟨PolygonalPath.segment (vertex b) (vertex (Fin.last m)), by simp,
      PolygonalPath.segment_terminal _ _, ?_, by simp⟩
    apply safePath_segment
    intro y hy hy'
    refine ⟨(simplex_vertex b).mix (simplex_vertex _) hy hy', ?_⟩
    rw [P.value_terminal_edge b hb]
    apply terminal_quadratic_safe_after _ _ _ 0 (P.residual_nonnegative _ _)
      (P.designated_nonnegative _) ?_ ?_ y hy
    · simpa only [zero_mul, mul_zero, sub_zero, one_pow, one_mul, add_zero]
        using hgood.trans_eq (P.value_vertex _ _)
    · simpa only [sub_zero, mul_one] using hno

private theorem actual_terminal_exit_right (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hderiv : 0 ≤ P.residual c (Fin.last m) - P.residual a (Fin.last m) -
      (1 - 2 * x) * P.overlap a c (Fin.last m))
    (hno : ¬ (P.residual c (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual c (Fin.last m) * x)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  let L := P.baseline (Fin.last m)
  let G := P.designated (Fin.last m)
  let u := P.residual a (Fin.last m)
  let v := P.residual c (Fin.last m)
  let o := P.overlap a c (Fin.last m)
  have hgoodpoly : (3 : ℝ) / 4 * (L + G) ≤ pairPolynomial L u v o x := by
    rw [P.value_mix_vertices _ _ _ hac] at hgood
    exact hgood
  have hsafe : ∀ z : ℝ, x ≤ z → z ≤ 1 →
      (3 : ℝ) / 4 * (L + G) ≤ pairPolynomial L u v o z := by
    intro z hxz _
    exact hgoodpoly.trans (pairPolynomial_mono_right L u v o x z
      (P.overlap_nonnegative _ _ _) hderiv hxz)
  have hendno : ¬ (v * (L + G) < G ^ 2 ∧ G < 2 * v) :=
    terminal_pair_endpoint_no_bad_minimum L G u v o x
      (P.baseline_nonnegative _) (P.designated_nonnegative _) (P.residual_nonnegative _ _)
      (hP.2 _ c) (hP.2 _ a) (P.terminal_overlap_lower_bound a c) hno hsafe
  have hendgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (vertex c) := by
    rw [P.value_vertex]
    simpa [pairPolynomial, L, G, v, benchmark] using hsafe 1 hx' le_rfl
  obtain ⟨δ, hδinitial, hδterminal, hδsafe, hδpieces⟩ :=
    P.terminal_vertex_exit c hendgood hendno
  let γ := PolygonalPath.segment (mix (vertex a) (vertex c) x) (vertex c)
  have hγsafe : SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ := by
    apply safePath_segment
    intro y hy hy'
    rw [mix_mix_right]
    have hz : 0 ≤ (1 - y) * x + y :=
      add_nonneg (mul_nonneg (sub_nonneg.mpr hy') hx) hy
    have hz' : (1 - y) * x + y ≤ 1 := by
      have := mul_nonneg (sub_nonneg.mpr hy') (sub_nonneg.mpr hx')
      nlinarith
    have hzx : x ≤ (1 - y) * x + y := by
      have := mul_nonneg hy (sub_nonneg.mpr hx')
      nlinarith
    refine ⟨(simplex_vertex a).mix (simplex_vertex c) hz hz', ?_⟩
    rw [P.value_mix_vertices _ _ _ hac]
    exact hsafe _ hzx hz'
  have hjoin : γ.node (Fin.last γ.pieces) = δ.node 0 :=
    (PolygonalPath.segment_terminal _ _).trans hδinitial.symm
  refine ⟨PolygonalPath.append γ δ, ?_, ?_, hγsafe.append hδsafe hjoin, ?_⟩
  · simp [γ]
  · rw [PolygonalPath.append_terminal γ δ hjoin, hδterminal]
  · simp only [PolygonalPath.append_pieces]
    change 1 + δ.pieces ≤ 2
    omega

/-- A terminal-good distinct pair of mass at most one half has a two-piece
exit when the anchor's terminal-partner quadratic excludes the bad minimum.
This is the geometric arbitrary-partner form of the actual exit lemma. -/
theorem actual_terminal_exit (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hno : ¬ (P.residual a (Fin.last m) * P.benchmark (Fin.last m) <
      P.designated (Fin.last m) ^ 2 ∧
      P.designated (Fin.last m) < 2 * P.residual a (Fin.last m) * (1 - x))) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  have hx' : x ≤ 1 := by linarith
  by_cases hd : 0 ≤ P.residual c (Fin.last m) - P.residual a (Fin.last m) -
      (1 - 2 * x) * P.overlap a c (Fin.last m)
  · apply P.actual_terminal_exit_right hP a c hac x hx hx' hgood hd
    rintro ⟨_, hbad⟩
    have h1 := mul_nonneg (P.residual_nonnegative c (Fin.last m))
      (show 0 ≤ 1 - 2 * x by linarith)
    have h2 := hP.2 (Fin.last m) c
    nlinarith
  · have hd' : 0 ≤ P.residual a (Fin.last m) - P.residual c (Fin.last m) -
        (1 - 2 * (1 - x)) * P.overlap c a (Fin.last m) := by
      rw [P.overlap_comm c a]
      linarith
    have hgood' : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
        P.value (Fin.last m) (mix (vertex c) (vertex a) (1 - x)) := by
      rw [← mix_swap]
      exact hgood
    obtain ⟨γ, hγinitial, hγterminal, hγsafe, hγpieces⟩ :=
      P.actual_terminal_exit_right hP c a (Ne.symm hac) (1 - x)
        (sub_nonneg.mpr hx') (by linarith) hgood' hd' hno
    refine ⟨γ, ?_, hγterminal, hγsafe, hγpieces⟩
    rw [hγinitial, ← mix_swap]

/-- The strong anchor budget and the raw envelope supply the actual
arbitrary-partner terminal exit. -/
theorem actual_terminal_exit_of_budget (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ) (hx : 0 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (hbudget : 3 ≤ P.designated a +
      2 * (P.baseline (Fin.last m) + P.residual a (Fin.last m)))
    (henv : 4 * (1 - x) * (P.designated a - P.residual a (Fin.last m)) ≤
      3 - 3 * P.designated (Fin.last m) + P.baseline (Fin.last m)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  apply P.actual_terminal_exit hP a c hac x hx hxhalf hgood
  exact actual_terminal_no_bad_minimum _ _ _ _ _
    (P.baseline_nonnegative _) (P.residual_nonnegative _ _) (hP.2 _ a)
    (P.designated_antitone hP (Fin.le_last a)) (by linarith) (by linarith) hbudget henv

/-- In the middle mass range, canonical persistence replaces the stronger
anchor budget in the actual terminal exit. -/
theorem actual_terminal_exit_of_canonical_budget (hP : P.Canonical)
    (a c : Fin (m + 1)) (hac : a ≠ c) (x : ℝ)
    (hxquarter : (1 : ℝ) / 4 ≤ x) (hxhalf : x ≤ 1 / 2)
    (hgood : (3 : ℝ) / 4 * P.benchmark (Fin.last m) ≤
      P.value (Fin.last m) (mix (vertex a) (vertex c) x))
    (henv : 4 * (1 - x) * (P.designated a - P.residual a (Fin.last m)) ≤
      3 - 3 * P.designated (Fin.last m) + P.baseline (Fin.last m)) :
    ∃ γ : PolygonalPath m,
      γ.node 0 = mix (vertex a) (vertex c) x ∧
      γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
  apply P.actual_terminal_exit hP a c hac x (by linarith) hxhalf hgood
  have hbudget : 1 ≤ P.baseline (Fin.last m) + P.residual a (Fin.last m) :=
    (P.one_le_benchmark hP a).trans (P.baseline_add_residual_monotone a (Fin.le_last a))
  exact actual_terminal_no_bad_minimum_canonical _ _ _ _ _
    (P.baseline_nonnegative _) (P.residual_nonnegative _ _) (hP.2 _ a)
    (P.designated_antitone hP (Fin.le_last a)) (by linarith) (by linarith) hbudget henv

end AtomicProfile
end ConsistentSubmodular
