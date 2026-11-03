module

public import ConsistentSubmodular.Deterministic.Basic.WindowBounds
public import ConsistentSubmodular.Deterministic.Basic.Paths

@[expose] public section

/-!
# An elementary certificate at level `1/√2` (Appendix B.2.2)

Theorem B.4 (prefix–suffix tradeoff), which gives Theorem 6 at `β = 1/√2`: the
anchor is the half mixture of the initial candidate `O_0` and the candidate
`O_c` of the last stage `c` whose credit `K_c = 2 g_c - r_c` of (25) meets the
envelope `D = max_j (2 K_j - 4 (1 - β) P_j)` of (27). The prefix bound
(Lemma B.5) covers the stages up to `c`, the suffix bound (Lemma B.6) the
stages after `c`. The entry is one segment and the exit two.

All values are compared through the two-type value `H_{R_j}(O_0, O_c; s)` of
(23) (`pairValue`, Appendix B.2.1). For the partner `c = 0` the paper uses a
second label for `O_0` and merges the two labels afterwards; here
`pairValue_le` shows directly that the merged value is at least the two-label
value, so the partner `c = 0` needs no separate treatment. The empty value of
the objective need not be zero.
-/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

namespace PolygonalPath

variable {m : ℕ}

/-- The path with the two segments from `p` to `q` and from `q` to `r`. -/
def twoSegments (p q r : Point m) : PolygonalPath m where
  pieces := 2
  node := ![p, q, r]

theorem along_segment {Φ : Point m → Prop} {p q : Point m}
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix p q x)) : (segment p q).Along Φ := by
  constructor
  · intro j
    fin_cases j
    · simpa using h 0 le_rfl zero_le_one
    · simpa [segment] using h 1 zero_le_one le_rfl
  · intro j x hx hx1
    fin_cases j
    simpa [segment] using h x hx hx1

theorem along_twoSegments {Φ : Point m → Prop} {p q r : Point m}
    (h1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix p q x))
    (h2 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Φ (mix q r x)) : (twoSegments p q r).Along Φ := by
  constructor
  · intro j
    fin_cases j
    · simpa using h1 0 le_rfl zero_le_one
    · simpa using h1 1 zero_le_one le_rfl
    · simpa using h2 1 zero_le_one le_rfl
  · intro j x hx hx1
    fin_cases j
    · simpa [twoSegments] using h1 x hx hx1
    · simpa [twoSegments] using h2 x hx hx1

end PolygonalPath

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The quantity `2 K_j - 4 (1 - β) P_j` whose maximum is the envelope `D` of (27). -/
def envelopeTerm (β : ℝ) (j : Fin (W.lastStage + 1)) : ℝ :=
  2 * W.credit j - 4 * (1 - β) * W.benchmark j

/-- `r_j ≥ 0`, by monotonicity. -/
theorem residual_nonneg (i j : Fin (W.lastStage + 1)) : 0 ≤ W.residual i j := by
  unfold residual arrivalValue
  linarith [W.objective.monotone _ _
    (Finset.subset_union_left : W.arrivals j ⊆ W.arrivals j ∪ W.candidate i)]

/-- `r_j ≤ g_j`, by the optimality of `O_j`. -/
theorem residual_le_gain (i j : Fin (W.lastStage + 1)) : W.residual i j ≤ W.gain j := by
  have h := W.candidate_optimal j (W.candidate i) (W.candidate_subset i) (W.candidate_card i)
  rw [Finset.union_comm (W.candidate i)] at h
  unfold residual gain benchmark
  linarith

theorem residual_self (j : Fin (W.lastStage + 1)) : W.residual j j = W.gain j := by
  simp [residual, gain, benchmark, Finset.union_comm]

/-- Inequality (26): the credit never exceeds the benchmark, `K_j ≤ P_j`. -/
theorem credit_le_benchmark (j : Fin (W.lastStage + 1)) : W.credit j ≤ W.benchmark j := by
  have hg := W.gain_antitone (Fin.zero_le j)
  have hA : W.objective.value (W.candidate 0) ≤
      W.objective.value (W.arrivals j ∪ W.candidate 0) :=
    W.objective.monotone _ _ Finset.subset_union_right
  have h0 := W.objective.nonnegative ∅
  have hz : W.gain 0 = W.objective.value (W.candidate 0) - W.objective.value ∅ := by
    simp [gain, benchmark, arrivalValue, W.arrivals_zero]
  unfold credit residual
  unfold gain at *
  linarith

/-- Moving from the midpoint toward the endpoint of larger residual does not
decrease the two-type value: by (23), its derivative is the endpoint difference
plus `(2s - 1) o`. -/
theorem pairValue_half_le (j a b : Fin (W.lastStage + 1)) (s : ℝ)
    (hs : 0 ≤ (s - 1 / 2) * (W.residual b j - W.residual a j)) :
    W.pairValue j a b (1 / 2) ≤ W.pairValue j a b s := by
  have ho := W.pair_submodular j a b
  have hsq := sq_nonneg (s - 1 / 2)
  unfold residual at hs
  unfold pairValue twoTypeValue
  nlinarith [mul_nonneg hsq (show 0 ≤ W.objective.value (W.arrivals j ∪ W.candidate a) +
    W.objective.value (W.arrivals j ∪ W.candidate b) -
    W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) -
    W.objective.value (W.arrivals j) by linarith)]

/-- Lemma B.5 (prefix bound), the inequality (29) multiplied by four. -/
theorem prefix_bound {j c : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c ≤ 4 * W.pairValue j 0 c (1 / 2) := by
  have hR := W.arrivals_mono hjc
  have h1 := W.objective.diminishing_returns hR (W.candidate c)
  have h2 := W.objective.diminishing_returns
    (Finset.union_subset_union_left hR : W.arrivals j ∪ W.candidate 0 ⊆
      W.arrivals c ∪ W.candidate 0) (W.candidate c)
  have h3 := W.objective.monotone (W.arrivals c ∪ W.candidate c)
    ((W.arrivals c ∪ W.candidate 0) ∪ W.candidate c) (by
      intro e he
      simp only [Finset.mem_union] at he ⊢
      tauto)
  have hassoc : (W.arrivals j ∪ W.candidate 0) ∪ W.candidate c =
      W.arrivals j ∪ (W.candidate 0 ∪ W.candidate c) := Finset.union_assoc _ _ _
  rw [hassoc] at h2
  have hcomm : W.benchmark c = W.objective.value (W.arrivals c ∪ W.candidate c) := by
    rw [benchmark, Finset.union_comm]
  unfold credit gain residual arrivalValue pairValue twoTypeValue
  rw [hcomm]
  nlinarith

/-- The midpoint bound (24) at stage `j`, with
`(u + z)/2 - min(u, z)/4 = (u + z + max(u, z))/4`: four times
`H_{R_j}(O_0, O_c; 1/2)` is at least `4 L_j`. -/
theorem half_pair_lower (j c : Fin (W.lastStage + 1)) :
    4 * W.arrivalValue j + W.residual 0 j + W.residual c j +
        max (W.residual 0 j) (W.residual c j) ≤ 4 * W.pairValue j 0 c (1 / 2) := by
  obtain ⟨h0, hc⟩ := W.pair_union_ge j 0 c
  unfold residual arrivalValue pairValue twoTypeValue
  rcases le_total (W.objective.value (W.arrivals j ∪ W.candidate 0))
    (W.objective.value (W.arrivals j ∪ W.candidate c)) with h | h
  · rw [max_eq_right (by linarith)]
    nlinarith
  · rw [max_eq_left (by linarith)]
    nlinarith

/-- The second exit edge, toward the terminal optimizer `O_m`, keeps
`λ_m + 3v/4`, where `v` is the terminal residual of its starting candidate. -/
theorem pairValue_terminal (b : Fin (W.lastStage + 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    W.arrivalValue (Fin.last W.lastStage) + 3 / 4 * W.residual b (Fin.last W.lastStage) ≤
      W.pairValue (Fin.last W.lastStage) b (Fin.last W.lastStage) s := by
  have hopt := W.candidate_optimal (Fin.last W.lastStage) (W.candidate b)
    (W.candidate_subset b) (W.candidate_card b)
  rw [Finset.union_comm (W.candidate b), Finset.union_comm (W.candidate _)] at hopt
  obtain ⟨hm, -⟩ := W.pair_union_ge (Fin.last W.lastStage) b (Fin.last W.lastStage)
  have hb := W.objective.monotone (W.arrivals (Fin.last W.lastStage))
    (W.arrivals (Fin.last W.lastStage) ∪ W.candidate b) Finset.subset_union_left
  have hq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hq0 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
  unfold residual arrivalValue pairValue twoTypeValue
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hb)]

end WindowInstance

/-- Lemma B.6 (suffix bound), the inequality (30) with `M` any upper bound of
`u` and `z` in place of `max(u, z)`. -/
theorem suffix_bound {lam g u z M γ : ℝ} (hz : 0 ≤ z) (hMu : u ≤ M) (hMz : z ≤ M)
    (hγ0 : 0 ≤ γ) (hγ2 : γ ≤ 2) (h : 2 * g - u ≤ γ * (lam + z)) :
    2 * (lam + g) ≤ (2 + γ) * (lam + (u + z + M) / 4) := by
  rcases le_total u z with huz | hzu
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMz),
      mul_nonneg (sub_nonneg.mpr hγ2) (show 0 ≤ 2 * z - u by linarith)]
  · nlinarith [mul_nonneg (show 0 ≤ 2 + γ by linarith) (sub_nonneg.mpr hMu),
      mul_nonneg hγ0 (sub_nonneg.mpr hzu), mul_nonneg (sub_nonneg.mpr hγ2) hz]

/-- The suffix ratio `1/(2β)` dominates every level `α` with `2 β α ≤ 1`. -/
theorem le_of_suffix_ratio {α β P X : ℝ} (hβ : 0 < β) (hα : 2 * β * α ≤ 1) (hP : 0 ≤ P)
    (h : 2 * P ≤ 4 * β * X) : α * P ≤ X := by
  by_contra hn
  have hlt := lt_of_not_ge hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hα) hP, mul_pos hβ (sub_pos.mpr hlt)]

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- The envelope `D = max_j (2 K_j - 4 (1 - β) P_j)` of (27). -/
def envelope (β : ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty (W.envelopeTerm β)

theorem envelopeTerm_le_envelope (β : ℝ) (j : Fin (W.lastStage + 1)) :
    W.envelopeTerm β j ≤ W.envelope β :=
  Finset.le_sup' _ (Finset.mem_univ j)

/-- The envelope is attained at an eligible stage `h`: `K_h ≥ D`, because
`K_h ≤ P_h` (26). Hence the last eligible index `c` of (27) exists. -/
theorem exists_envelope_eligible {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ h, W.envelopeTerm β h = W.envelope β ∧ W.envelope β ≤ W.credit h := by
  obtain ⟨h, -, hh⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (W.envelopeTerm β)
  refine ⟨h, hh.symm, ?_⟩
  rw [envelope, hh]
  have hK := W.credit_le_benchmark h
  have hP := W.benchmark_nonneg h
  simp only [envelopeTerm]
  nlinarith

/-- The requirement behind the envelope: at every stage `j`,
`4 β P_j ≤ 4 λ_j + 2 r_j + K_c` once `K_c ≥ D`. -/
theorem envelope_requirement {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (j : Fin (W.lastStage + 1)) :
    4 * β * W.benchmark j ≤ 4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c := by
  have hm := W.envelopeTerm_le_envelope β j
  simp only [envelopeTerm, credit, gain] at hm hDc ⊢
  linarith

/-- Persistence on the prefix (Theorem B.4): for `j ≤ c`, Lemma B.5 and the
envelope give `H_{R_j}(O_0, O_c; 1/2) ≥ β P_j`. -/
theorem halfMixture_prefix {β : ℝ} {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) {j : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    β * W.benchmark j ≤ W.pairValue j 0 c (1 / 2) := by
  have hb := W.prefix_bound hjc
  have := W.envelope_requirement hDc j
  linarith

/-- Persistence on the suffix (Theorem B.4): for `j > c`, last eligibility and
the benchmark credit (31) of the partner give the premise (32) of Lemma B.6,
so the reserve `L_j` of (33) is at least `α P_j` for every `α` with
`2 β α ≤ 1`. -/
theorem halfMixture_suffix {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hafter : ∀ j, c < j → W.credit j < W.envelope β)
    {j : Fin (W.lastStage + 1)} (hcj : c < j) :
    α * W.benchmark j ≤ W.arrivalValue j +
      (W.residual 0 j + W.residual c j + max (W.residual 0 j) (W.residual c j)) / 4 := by
  have hγ : 0 ≤ 4 * β - 2 := by linarith
  obtain ⟨h, hh, hhK⟩ := W.exists_envelope_eligible hβ'
  have hhc : h ≤ c := by
    by_contra hn
    exact absurd hhK (not_le.mpr (hafter h (lt_of_not_ge hn)))
  -- The benchmark credit (31) of the partner: `D ≤ γ P_h ≤ γ P_c`.
  have hDP : W.envelope β ≤ (4 * β - 2) * W.benchmark c := by
    have hK := W.credit_le_benchmark h
    have hPh := mul_le_mul_of_nonneg_left (W.benchmark_mono hhc) hγ
    rw [← hh]
    simp only [envelopeTerm]
    nlinarith
  have hPc : W.benchmark c ≤ W.arrivalValue j + W.residual c j := by
    have hm := W.objective.monotone (W.candidate c ∪ W.arrivals c)
      (W.arrivals j ∪ W.candidate c) (by
        intro e he
        have hR := W.arrivals_mono hcj.le
        simp only [Finset.mem_union] at he ⊢
        rcases he with he | he
        · exact Or.inr he
        · exact Or.inl (hR he))
    simp only [residual, benchmark] at hm ⊢
    linarith
  have hK := hafter j hcj
  -- Last eligibility gives the premise (32) of Lemma B.6.
  have hpremise : 2 * W.gain j - W.residual 0 j ≤
      (4 * β - 2) * (W.arrivalValue j + W.residual c j) := by
    have := mul_le_mul_of_nonneg_left hPc hγ
    simp only [credit] at hK
    linarith
  have hs := suffix_bound (lam := W.arrivalValue j) (W.residual_nonneg c j)
    (le_max_left _ _) (le_max_right _ _) hγ (by linarith) hpremise
  have h2 : 2 + (4 * β - 2) = 4 * β := by ring
  rw [h2, ← W.benchmark_eq j] at hs
  exact le_of_suffix_ratio (by linarith) hα (W.benchmark_nonneg j) hs

/-- Theorem B.4. For `1/2 ≤ β ≤ 3/4` and every level `α` with `α ≤ β` and
`2 β α ≤ 1`, the half mixture of `O_0` and the last eligible partner `O_c` is the
anchor of a certificate with one entry segment and two exit segments. -/
theorem halfMixture_certificate {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hαβ : α ≤ β) (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (hafter : ∀ j, c < j → W.credit j < W.envelope β) :
    ∃ Z : W.Certificate α 3, Z.anchor = mix (vertex 0) (vertex c) (1 / 2) ∧
      Z.entry.pieces = 1 ∧ Z.exit.pieces = 2 := by
  classical
  have hprefix (j : Fin (W.lastStage + 1)) (hjc : j ≤ c) :
      β * W.benchmark j ≤ W.pairValue j 0 c (1 / 2) := W.halfMixture_prefix hDc hjc
  have hsuffix (j : Fin (W.lastStage + 1)) (hcj : c < j) :
      α * W.benchmark j ≤ W.arrivalValue j +
        (W.residual 0 j + W.residual c j + max (W.residual 0 j) (W.residual c j)) / 4 :=
    W.halfMixture_suffix hβ hβ' hα hafter hcj
  -- The anchor and its persistence.
  let p : Point W.lastStage := mix (vertex 0) (vertex c) (1 / 2)
  have hp : IsSimplex p := (simplex_vertex 0).mix (simplex_vertex c) (by norm_num) (by norm_num)
  have hpersist (j : Fin (W.lastStage + 1)) : α * W.benchmark j ≤ W.mixtureValue j p := by
    have hpair := W.pairValue_le j 0 c (s := 1 / 2) (by norm_num) (by norm_num)
    rcases le_or_gt j c with hjc | hcj
    · have hb := hprefix j hjc
      have hPj := W.benchmark_nonneg j
      nlinarith [mul_le_mul_of_nonneg_right hαβ hPj]
    · have hl := W.half_pair_lower j c
      have hs := hsuffix j hcj
      linarith
  -- The exit reserve `L_m ≥ α P_m` at the terminal stage.
  have hreserve : α * W.benchmark (Fin.last W.lastStage) ≤
      W.arrivalValue (Fin.last W.lastStage) +
        (W.residual 0 (Fin.last W.lastStage) + W.residual c (Fin.last W.lastStage) +
          max (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))) / 4 := by
    rcases lt_or_eq_of_le (Fin.le_last c) with hcl | hcl
    · exact hsuffix _ hcl
    · have hb := W.envelope_requirement hDc (Fin.last W.lastStage)
      rw [hcl] at hb ⊢
      rw [residual_self]
      have hug := W.residual_le_gain 0 (Fin.last W.lastStage)
      rw [max_eq_right hug]
      have hPm := W.benchmark_nonneg (Fin.last W.lastStage)
      unfold credit at hb
      nlinarith [mul_le_mul_of_nonneg_right hαβ hPm]
  have hmid := W.half_pair_lower (Fin.last W.lastStage) c
  -- The exit partner: the endpoint with larger terminal residual.
  obtain ⟨b, hbres, hbside⟩ : ∃ b : Fin (W.lastStage + 1),
      W.residual b (Fin.last W.lastStage) =
        max (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage)) ∧
      ((b = c ∧ W.residual 0 (Fin.last W.lastStage) ≤ W.residual c (Fin.last W.lastStage)) ∨
        (b = 0 ∧ W.residual c (Fin.last W.lastStage) ≤ W.residual 0 (Fin.last W.lastStage))) := by
    rcases le_total (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
      with huz | hzu
    · exact ⟨c, (max_eq_right huz).symm, Or.inl ⟨rfl, huz⟩⟩
    · exact ⟨0, (max_eq_left hzu).symm, Or.inr ⟨rfl, hzu⟩⟩
  have hexit1 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark (Fin.last W.lastStage) ≤
        W.mixtureValue (Fin.last W.lastStage) (mix p (vertex b) x) := by
    rcases hbside with ⟨hbc, huz⟩ | ⟨hb0, hzu⟩
    · have hmixeq : mix p (vertex b) x = mix (vertex 0) (vertex c) ((1 - x) * (1 / 2) + x) := by
        rw [hbc]
        exact mix_mix_right _ _ _ _
      rw [hmixeq]
      have hpair := W.pairValue_le (Fin.last W.lastStage) 0 c
        (s := (1 - x) * (1 / 2) + x) (by nlinarith) (by nlinarith)
      have hmono := W.pairValue_half_le (Fin.last W.lastStage) 0 c ((1 - x) * (1 / 2) + x)
        (by nlinarith)
      linarith
    · have hmixeq : mix p (vertex b) x = mix (vertex 0) (vertex c) ((1 - x) * (1 / 2)) := by
        rw [hb0]
        exact mix_mix_left _ _ _ _
      rw [hmixeq]
      have hpair := W.pairValue_le (Fin.last W.lastStage) 0 c
        (s := (1 - x) * (1 / 2)) (by nlinarith) (by nlinarith)
      have hmono := W.pairValue_half_le (Fin.last W.lastStage) 0 c ((1 - x) * (1 / 2))
        (by nlinarith)
      linarith
  have hexit2 (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark (Fin.last W.lastStage) ≤
        W.mixtureValue (Fin.last W.lastStage) (mix (vertex b) (vertex (Fin.last W.lastStage)) x) := by
    have hpair := W.pairValue_le (Fin.last W.lastStage) b (Fin.last W.lastStage) hx hx1
    have hterm := W.pairValue_terminal b hx hx1
    rw [hbres] at hterm
    have h1 := le_max_left (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
    have h2 := le_max_right (W.residual 0 (Fin.last W.lastStage)) (W.residual c (Fin.last W.lastStage))
    linarith
  -- The entry segment stays above the midpoint value at stage zero.
  have hentry (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
      α * W.benchmark 0 ≤ W.mixtureValue 0 (mix (vertex 0) p x) := by
    have hmixeq : mix (vertex 0) p x = mix (vertex 0) (vertex c) (x * (1 / 2)) := by
      funext i
      simp only [p, mix]
      ring
    rw [hmixeq]
    have hpair := W.pairValue_le 0 0 c (s := x * (1 / 2)) (by nlinarith) (by nlinarith)
    have hopt : W.residual c 0 ≤ W.residual 0 0 := by
      have h := W.residual_le_gain c 0
      rwa [← W.residual_self 0] at h
    have hmono := W.pairValue_half_le 0 0 c (x * (1 / 2)) (by nlinarith)
    have hb := hprefix 0 (Fin.zero_le c)
    have hP0 := W.benchmark_nonneg 0
    nlinarith [mul_le_mul_of_nonneg_right hαβ hP0]
  exact ⟨{
    anchor := p
    entry := PolygonalPath.segment (vertex 0) p
    exit := PolygonalPath.twoSegments p (vertex b) (vertex (Fin.last W.lastStage))
    anchor_mem := hp
    entry_mem := PolygonalPath.along_segment (fun x hx hx1 =>
      (simplex_vertex 0).mix hp hx hx1)
    exit_mem := PolygonalPath.along_twoSegments
      (fun x hx hx1 => hp.mix (simplex_vertex b) hx hx1)
      (fun x hx hx1 => (simplex_vertex b).mix (simplex_vertex _) hx hx1)
    entry_start := rfl
    entry_finish := PolygonalPath.segment_terminal _ _
    exit_start := rfl
    exit_finish := rfl
    persistence := hpersist
    safe_entry := PolygonalPath.along_segment hentry
    safe_exit := PolygonalPath.along_twoSegments hexit1 hexit2
    segments := le_rfl }, rfl, rfl, rfl⟩

/-- The last eligible partner `c = max {j : K_j ≥ D}` of (27). -/
theorem exists_last_eligible {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ c : Fin (W.lastStage + 1), W.envelope β ≤ W.credit c ∧
      ∀ j, c < j → W.credit j < W.envelope β := by
  classical
  obtain ⟨h, -, hhK⟩ := W.exists_envelope_eligible hβ'
  let E : Finset (Fin (W.lastStage + 1)) :=
    Finset.univ.filter (fun j => W.envelope β ≤ W.credit j)
  have hhE : h ∈ E := by simpa [E] using hhK
  refine ⟨E.max' ⟨h, hhE⟩, (Finset.mem_filter.mp (E.max'_mem ⟨h, hhE⟩)).2, ?_⟩
  intro j hcj
  by_contra hn
  have hjE : j ∈ E := by
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_of_not_gt hn
  exact absurd (E.le_max' j hjE) (not_le.mpr hcj)

/-- Theorem B.4 for one window and every admissible level. -/
theorem exists_halfMixtureCertificate {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hαβ : α ≤ β) (hα : 2 * β * α ≤ 1) : Nonempty (W.Certificate α 3) := by
  obtain ⟨c, hDc, hafter⟩ := W.exists_last_eligible hβ'
  obtain ⟨Z, -⟩ := W.halfMixture_certificate hβ hβ' hαβ hα hDc hafter
  exact ⟨Z⟩

end WindowInstance

theorem one_div_sqrt_two_bounds :
    1 / 2 ≤ 1 / Real.sqrt 2 ∧ 1 / Real.sqrt 2 ≤ 3 / 4 ∧
      2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ 1 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by norm_num) hpos]
    nlinarith
  · rw [div_le_div_iff₀ hpos (by norm_num)]
    nlinarith
  · have he : 2 * (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 2 / (Real.sqrt 2 * Real.sqrt 2) := by
      field_simp
    rw [he, hs]
    norm_num

namespace Certificates

/-- Theorem 6: every window admits a `(1/√2, 3)`-certificate. This is
Theorem B.4 at `β = 1/√2`, where `α(β) = β = 1/(2β)`. -/
theorem sqrtTwoCertificates : SqrtTwoCertificatesGoal := by
  intro _ W
  obtain ⟨h1, h2, h3⟩ := one_div_sqrt_two_bounds
  exact W.exists_halfMixtureCertificate h1 h2 le_rfl h3

/-- Lemma B.5 (prefix bound). -/
theorem prefixBound : PrefixBoundGoal := by
  intro n W j c hjc
  have h := W.prefix_bound hjc
  change 4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c ≤
    4 * W.pairValue j 0 c (1 / 2) at h
  unfold WindowInstance.pairValue at h
  linarith

/-- Lemma B.6 (suffix bound). -/
theorem suffixBound : SuffixBoundGoal := by
  intro lam g u z γ _ _ _ hz hγ0 hγ2 h
  have hs := suffix_bound (M := max u z) hz (le_max_left u z) (le_max_right u z) hγ0 hγ2 h
  have hminmax : lam + (u + z) / 2 - min u z / 4 = lam + (u + z + max u z) / 4 := by
    rcases le_total u z with huz | hzu
    · rw [min_eq_left huz, max_eq_right huz]; ring
    · rw [min_eq_right hzu, max_eq_left hzu]; ring
  rw [hminmax, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith [mul_comm (2 + γ) (lam + (u + z + max u z) / 4)]

/-- Theorem B.4 (prefix–suffix tradeoff). -/
theorem prefixSuffixTradeoff : PrefixSuffixTradeoffGoal := by
  intro β hβ hβ' n W
  have hβ0 : 0 < β := by linarith
  have hhalf : 2 * β * (1 / (2 * β)) = 1 := by field_simp
  obtain ⟨h, -, hhK⟩ := W.exists_envelope_eligible hβ'
  refine ⟨⟨h, hhK⟩, fun c hDc hafter => ⟨fun j hjc => W.halfMixture_prefix hDc hjc,
    fun j hcj => ?_, ?_⟩⟩
  · have hs := W.halfMixture_suffix (α := 1 / (2 * β)) hβ.le hβ' hhalf.le hafter hcj
    have hl := W.half_pair_lower j c
    have heq : W.benchmark j / (2 * β) = 1 / (2 * β) * W.benchmark j := by ring
    change W.benchmark j / (2 * β) ≤ W.pairValue j 0 c (1 / 2)
    linarith
  · have hlevel : 2 * β * min β (1 / (2 * β)) ≤ 1 := by
      calc 2 * β * min β (1 / (2 * β)) ≤ 2 * β * (1 / (2 * β)) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
        _ = 1 := hhalf
    obtain ⟨Z, hZ, he, hx⟩ := W.halfMixture_certificate (α := min β (1 / (2 * β))) hβ.le hβ'
      (min_le_left _ _) hlevel hDc hafter
    exact ⟨Z, hZ, he, hx.le⟩

end Certificates

end ConsistentSubmodular
