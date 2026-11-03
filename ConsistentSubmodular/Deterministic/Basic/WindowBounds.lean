module

public import ConsistentSubmodular.Deterministic.Basic.PhysicalSampling
public import ConsistentSubmodular.Deterministic.Basic.Simplex

@[expose] public section

/-!
# Window bounds and mixture comparisons (Appendix B.2.1)

Lemma B.1 (window bounds): along a window the arrival value `λ_j` and the
benchmark `P_j` are nondecreasing, the residual `g_j = P_j - λ_j` is
nonincreasing, and the benchmark grows no faster than the arrivals alone (19).

Lemma B.2 (mixture comparisons): the value `H_Q(p)` of a type vector is at most
the multilinear extension `F_Q` at its physical vector `z(p)` (21), and at most
the linear average `Σ_i p_i f(Q ∪ O_i)` (22). The proof of (21) replaces the
paper's separate-concavity argument by independent block-coin replacement
(`physical_multilinear_lift`).

Lemma B.3 (two-type interpolation): along the edge between two cores, the value
`H_Q(A, B; s)` is the linear interpolation of the endpoint values less an
overlap penalty (23), which gives the midpoint bound (24) and keeps three
quarters of any common value of the endpoints.

The appendix normalizes `f(∅) = 0`; none of the three lemmas needs it.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem finiteExpectation_eq_sampleExpectation [Fintype ι] (p : ι → ℝ) (U : Finset ι)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    finiteExpectation p v = sampleExpectation U p v := by
  rw [← sampleExpectation_univ, sampleExpectation_inter_zero U Finset.univ p hp,
    Finset.univ_inter]

theorem sampleExpectation_singleton (p : ι → ℝ) (a : ι) (v : Finset ι → ℝ) :
    sampleExpectation {a} p v = (1 - p a) * v ∅ + p a * v {a} := by
  have h := sampleExpectation_insert (∅ : Finset ι) (Finset.notMem_empty a) p v
  simpa using h

theorem sampleExpectation_pair (p : ι → ℝ) {a b : ι} (hab : a ≠ b) (v : Finset ι → ℝ) :
    sampleExpectation {a, b} p v =
      (1 - p a) * ((1 - p b) * v ∅ + p b * v {b}) +
        p a * ((1 - p b) * v {a} + p b * v {a, b}) := by
  rw [sampleExpectation_insert {b} (by simpa using hab) p v, sampleExpectation_singleton,
    sampleExpectation_singleton]
  rfl

/-- The random set `I(p)` contains `i` with probability `p i`. -/
theorem finiteExpectation_mem [Fintype ι] (p : ι → ℝ) (i : ι) :
    finiteExpectation p (fun I => if i ∈ I then 1 else 0) = p i := by
  have h := finiteExpectation_hit p {i}
  have hfun : (fun I : Finset ι => if ({i} ∩ I).Nonempty then (1 : ℝ) else 0) =
      fun I => if i ∈ I then 1 else 0 := by
    funext I
    have hiff : ({i} ∩ I).Nonempty ↔ i ∈ I := by
      constructor
      · rintro ⟨x, hx⟩
        obtain ⟨hxi, hxI⟩ := Finset.mem_inter.mp hx
        rwa [Finset.mem_singleton.mp hxi] at hxI
      · exact fun hiI => ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, hiI⟩⟩
    simp only [hiff]
  rw [hfun] at h
  rw [h, Finset.prod_singleton]
  ring

namespace Objective

variable {n : ℕ} (f : Objective n)

/-- Subadditivity after contracting `Q`:
`f(Q ∪ ⋃_{i ∈ I} O_i) - f(Q) ≤ Σ_{i ∈ I} (f(Q ∪ O_i) - f(Q))`. -/
theorem value_biUnion_le (Q : Finset (Fin n)) {d : ℕ} (cores : Fin d → Finset (Fin n))
    (I : Finset (Fin d)) :
    f.value (Q ∪ I.biUnion cores) ≤ f.value Q + ∑ i ∈ I, (f.value (Q ∪ cores i) - f.value Q) := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have hdr := f.diminishing_returns (Finset.subset_union_left : Q ⊆ Q ∪ I.biUnion cores)
      (cores i)
    have hset : Q ∪ (cores i ∪ I.biUnion cores) = (Q ∪ I.biUnion cores) ∪ cores i := by
      ext e
      simp only [Finset.mem_union]
      tauto
    rw [hset]
    linarith

end Objective

namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-! ### Lemma B.1 -/

theorem benchmark_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.benchmark j :=
  W.objective.nonnegative _

theorem arrivalValue_mono : Monotone W.arrivalValue := fun _ _ hsj =>
  W.objective.monotone _ _ (W.arrivals_mono hsj)

theorem benchmark_mono : Monotone W.benchmark := by
  intro s j hsj
  unfold benchmark
  exact (W.objective.monotone _ _ (Finset.union_subset_union_right (W.arrivals_mono hsj))).trans
    (W.candidate_optimal j _ (W.candidate_subset s) (W.candidate_card s))

theorem benchmark_eq (j : Fin (W.lastStage + 1)) : W.benchmark j = W.arrivalValue j + W.gain j := by
  simp [gain]

/-- The optimum grows no faster than the arrivals alone, the second chain of
(19): `P_j - P_s ≤ λ_j - λ_s` for `s ≤ j`. The candidate `O_j` is feasible at
stage `s`, and diminishing returns compare the arrivals with and without it. -/
theorem benchmark_growth {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) :
    W.benchmark j - W.benchmark s ≤ W.arrivalValue j - W.arrivalValue s := by
  have hopt := W.candidate_optimal s (W.candidate j) (W.candidate_subset j) (W.candidate_card j)
  have hdr := W.objective.diminishing_returns
    (Finset.subset_union_right : W.arrivals s ⊆ W.candidate j ∪ W.arrivals s) (W.arrivals j)
  have h1 : (W.candidate j ∪ W.arrivals s) ∪ W.arrivals j = W.candidate j ∪ W.arrivals j := by
    rw [Finset.union_assoc, Finset.union_eq_right.mpr (W.arrivals_mono hsj)]
  rw [h1, Finset.union_eq_right.mpr (W.arrivals_mono hsj)] at hdr
  unfold benchmark arrivalValue
  linarith

theorem gain_antitone {s j : Fin (W.lastStage + 1)} (hsj : s ≤ j) : W.gain j ≤ W.gain s := by
  have h := W.benchmark_growth hsj
  unfold gain
  linarith

/-- `g_j ≥ 0`, because the empty core is feasible. -/
theorem gain_nonneg (j : Fin (W.lastStage + 1)) : 0 ≤ W.gain j := by
  have h := W.candidate_optimal j ∅ (Finset.empty_subset _) (by simp)
  rw [Finset.empty_union] at h
  unfold gain benchmark arrivalValue
  linarith

/-- `g_j ≤ V`: the residual decreases from `g_0 = V - f(∅)`. -/
theorem gain_le_benchmark_zero (j : Fin (W.lastStage + 1)) : W.gain j ≤ W.benchmark 0 := by
  have h := W.gain_antitone (Fin.zero_le j)
  have h0 := W.objective.nonnegative ∅
  have hg0 : W.gain 0 = W.benchmark 0 - W.objective.value ∅ := by
    simp [gain, arrivalValue, W.arrivals_zero]
  linarith

/-! ### Lemma B.2 -/

theorem bufferMixtureValue_eq_expectation (Q : Finset (Fin n)) (p : Point W.lastStage) :
    W.bufferMixtureValue Q p =
      finiteExpectation p (fun I => W.objective.value (Q ∪ I.biUnion W.candidate)) := rfl

/-- `H_{R_j} = H_j`. -/
theorem mixtureValue_eq_bufferMixtureValue (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.mixtureValue j p = W.bufferMixtureValue (W.arrivals j) p := rfl

/-- Inequality (21): `H_Q(p) ≤ F_Q(z(p))` on the type cube with mass at most
one. The lift `physical_multilinear_lift` samples over all elements; `z(p)`
vanishes off `V_now`, so the multilinear extension over `V_now` is the same. -/
theorem bufferMixtureValue_le_multilinearExtension (Q : Finset (Fin n)) (p : Point W.lastStage)
    (hp : ∀ i, 0 ≤ p i) (hmass : ∑ i, p i ≤ 1) :
    W.bufferMixtureValue Q p ≤ W.multilinearExtension Q (W.physicalVector p) := by
  have h := physical_multilinear_lift W.objective W.candidate Q p hp hmass
  have hzero : ∀ e ∉ W.present, physicalProbability W.candidate p e = 0 := by
    intro e he
    unfold physicalProbability
    exact Finset.sum_eq_zero fun i _ => if_neg fun hi => he (W.candidate_subset i hi)
  rw [finiteExpectation_eq_sampleExpectation _ W.present hzero] at h
  exact h

/-- Inequality (22): for a mixture `p ∈ Δ`, `H_Q(p) ≤ Σ_i p_i f(Q ∪ O_i)`, by
subadditivity after contracting `Q` and `P(i ∈ I(p)) = p_i`. -/
theorem bufferMixtureValue_le_average (Q : Finset (Fin n)) {p : Point W.lastStage}
    (hp : IsSimplex p) :
    W.bufferMixtureValue Q p ≤ ∑ i, p i * W.objective.value (Q ∪ W.candidate i) := by
  have hcube : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i =>
    ⟨hp.1 i, hp.2 ▸ Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)⟩
  let d : Fin (W.lastStage + 1) → ℝ := fun i =>
    W.objective.value (Q ∪ W.candidate i) - W.objective.value Q
  have hpoint : ∀ I : Finset (Fin (W.lastStage + 1)),
      W.objective.value (Q ∪ I.biUnion W.candidate) ≤
        W.objective.value Q + ∑ i, d i * (if i ∈ I then 1 else 0) := by
    intro I
    have h := W.objective.value_biUnion_le Q W.candidate I
    have hs : ∑ i ∈ I, d i = ∑ i, d i * (if i ∈ I then 1 else 0) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [← hs]
    exact h
  have hmono := finiteExpectation_mono p hcube hpoint
  have hE : finiteExpectation p
      (fun I => W.objective.value Q + ∑ i, d i * (if i ∈ I then 1 else 0)) =
      W.objective.value Q + ∑ i, d i * p i := by
    simp only [finiteExpectation_add, finiteExpectation_const, finiteExpectation_sum,
      finiteExpectation_mul, finiteExpectation_mem]
  rw [hE] at hmono
  have hd : ∑ i, d i * p i =
      ∑ i, p i * W.objective.value (Q ∪ W.candidate i) - W.objective.value Q * ∑ i, p i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [d]; ring
  rw [hd, hp.2] at hmono
  exact hmono.trans_eq (by ring)

/-! ### The two-type value of window candidates -/

/-- The two-type objective `H_{R_j}(O_a, O_b; s)` at stage `j`, summed over the four
outcomes of the two independent type samples. It equals the value of the mixture
`(1 - s) δ_a + s δ_b` when `a ≠ b`, and is a lower bound for it when `a = b`. -/
def pairValue (j a b : Fin (W.lastStage + 1)) (s : ℝ) : ℝ :=
  twoTypeValue W.objective (W.arrivals j) (W.candidate a) (W.candidate b) s

/-- The residual overlap is nonnegative. -/
theorem pair_submodular (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) +
        W.objective.value (W.arrivals j) ≤
      W.objective.value (W.arrivals j ∪ W.candidate a) +
        W.objective.value (W.arrivals j ∪ W.candidate b) := by
  have hs := W.objective.submodular (W.arrivals j ∪ W.candidate a) (W.arrivals j ∪ W.candidate b)
  have hu : (W.arrivals j ∪ W.candidate a) ∪ (W.arrivals j ∪ W.candidate b) =
      W.arrivals j ∪ (W.candidate a ∪ W.candidate b) := by
    ext e
    simp only [Finset.mem_union]
    tauto
  have hm := W.objective.monotone (W.arrivals j)
    ((W.arrivals j ∪ W.candidate a) ∩ (W.arrivals j ∪ W.candidate b))
    (Finset.subset_inter Finset.subset_union_left Finset.subset_union_left)
  rw [hu] at hs
  linarith

theorem pair_union_ge (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ W.candidate a) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) ∧
      W.objective.value (W.arrivals j ∪ W.candidate b) ≤
        W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) := by
  constructor <;> apply W.objective.monotone <;> intro e he <;>
    simp only [Finset.mem_union] at he ⊢ <;> tauto

theorem mixtureValue_vertex (j i : Fin (W.lastStage + 1)) :
    W.mixtureValue j (vertex i) = W.objective.value (W.arrivals j ∪ W.candidate i) := by
  change finiteExpectation (vertex i)
    (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate)) = _
  rw [finiteExpectation_eq_sampleExpectation _ {i} (fun k hk => by
      simp only [Finset.mem_singleton] at hk
      simp [vertex, hk]),
    sampleExpectation_singleton]
  simp [vertex]

/-- The value of the edge between `δ_a` and `δ_b` at stage `j` is the two-type
value (23) when `a ≠ b`, and at least it when `a = b`, since merging the two
labels of one core can only increase every value. -/
theorem pairValue_le (j a b : Fin (W.lastStage + 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    W.pairValue j a b s ≤ W.mixtureValue j (mix (vertex a) (vertex b) s) := by
  by_cases hab : a = b
  · subst b
    rw [mix_self, mixtureValue_vertex]
    have hm := W.objective.monotone (W.arrivals j) (W.arrivals j ∪ W.candidate a)
      Finset.subset_union_left
    have hq : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    unfold pairValue twoTypeValue
    rw [Finset.union_self]
    nlinarith
  · have hpa : mix (vertex a) (vertex b) s a = 1 - s := by
      simp [mix, vertex, hab]
    have hpb : mix (vertex a) (vertex b) s b = s := by
      simp [mix, vertex, Ne.symm hab]
    change _ ≤ finiteExpectation (mix (vertex a) (vertex b) s)
      (fun I => W.objective.value (W.arrivals j ∪ I.biUnion W.candidate))
    rw [finiteExpectation_eq_sampleExpectation _ {a, b} (fun k hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        simp [mix, vertex, hk.1, hk.2]),
      sampleExpectation_pair _ hab, hpa, hpb]
    have hU : ({a, b} : Finset (Fin (W.lastStage + 1))).biUnion W.candidate =
        W.candidate a ∪ W.candidate b := by
      rw [Finset.biUnion_insert, Finset.singleton_biUnion]
    simp only [Finset.biUnion_empty, Finset.union_empty, Finset.singleton_biUnion, hU]
    unfold pairValue twoTypeValue
    apply le_of_eq
    ring

end WindowInstance

/-! ### Lemma B.3 -/

section TwoType

variable {n : ℕ} (f : Objective n) (Q A B : Finset (Fin n))

/-- Formula (23): `H_Q(A, B; s) = λ + (1 - s) a + s b - s (1 - s) o`. -/
theorem twoTypeValue_eq (s : ℝ) :
    twoTypeValue f Q A B s = f.value Q + (1 - s) * (f.value (Q ∪ A) - f.value Q) +
      s * (f.value (Q ∪ B) - f.value Q) -
      s * (1 - s) * (f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q) := by
  unfold twoTypeValue
  ring

/-- Monotonicity bounds the residual overlap by both residuals:
`o ≤ min(a, b)`. -/
theorem overlap_le :
    f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q ≤
        f.value (Q ∪ A) - f.value Q ∧
      f.value (Q ∪ A) + f.value (Q ∪ B) - f.value (Q ∪ (A ∪ B)) - f.value Q ≤
        f.value (Q ∪ B) - f.value Q := by
  have hB := f.monotone (Q ∪ B) (Q ∪ (A ∪ B)) (by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    tauto)
  have hA := f.monotone (Q ∪ A) (Q ∪ (A ∪ B)) (by
    intro e he
    simp only [Finset.mem_union] at he ⊢
    tauto)
  constructor <;> linarith

/-- Inequality (24): at the midpoint,
`H_Q(A, B; 1/2) ≥ λ + (a + b)/2 - min(a, b)/4`. -/
theorem twoTypeValue_half_ge :
    f.value Q + ((f.value (Q ∪ A) - f.value Q) + (f.value (Q ∪ B) - f.value Q)) / 2 -
        min (f.value (Q ∪ A) - f.value Q) (f.value (Q ∪ B) - f.value Q) / 4 ≤
      twoTypeValue f Q A B (1 / 2) := by
  obtain ⟨hoa, hob⟩ := overlap_le f Q A B
  rw [twoTypeValue_eq]
  rcases le_total (f.value (Q ∪ A) - f.value Q) (f.value (Q ∪ B) - f.value Q) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- The last claim of Lemma B.3: if both cores have value at least `w` under the
buffer `Q`, every point of the edge has value at least `3w/4`. -/
theorem three_quarter_le_twoTypeValue {w : ℝ} (hwA : w ≤ f.value (Q ∪ A))
    (hwB : w ≤ f.value (Q ∪ B)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    3 / 4 * w ≤ twoTypeValue f Q A B s := by
  obtain ⟨hoa, hob⟩ := overlap_le f Q A B
  have hA := f.monotone Q (Q ∪ A) Finset.subset_union_left
  have hB := f.monotone Q (Q ∪ B) Finset.subset_union_left
  have hlam := f.nonnegative Q
  have hq0 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
  have hq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  rw [twoTypeValue_eq]
  -- With `v = min(a, b)`, the value is at least `λ + (1 - s(1 - s)) v ≥ λ + 3v/4`.
  rcases le_total (f.value (Q ∪ A)) (f.value (Q ∪ B)) with h | h
  · nlinarith [mul_le_mul_of_nonneg_left hoa hq0, mul_nonneg hs0 (sub_nonneg.mpr h),
      mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hA)]
  · nlinarith [mul_le_mul_of_nonneg_left hob hq0, mul_nonneg (show 0 ≤ 1 - s by linarith)
      (sub_nonneg.mpr h), mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hB)]

end TwoType

namespace WindowBounds

/-- **Lemma B.1** (window bounds). -/
theorem windowBounds : WindowBoundsGoal := fun _ W =>
  ⟨W.arrivalValue_mono, W.benchmark_mono, fun _ _ hsj => W.gain_antitone hsj,
    fun _ j hsj => ⟨W.gain_nonneg j, W.gain_le_benchmark_zero j, W.benchmark_mono (Fin.zero_le j),
      sub_nonneg.mpr (W.benchmark_mono hsj), W.benchmark_growth hsj⟩⟩

/-- **Lemma B.2** (mixture comparisons). -/
theorem mixtureComparisons : MixtureComparisonsGoal := fun _ W Q =>
  ⟨fun p hp hmass => W.bufferMixtureValue_le_multilinearExtension Q p hp hmass,
    fun _ hp => W.bufferMixtureValue_le_average Q hp⟩

/-- **Lemma B.3** (two-type interpolation). -/
theorem twoTypeInterpolation : TwoTypeInterpolationGoal := by
  intro n f Q A B
  dsimp only
  exact ⟨fun s _ _ => twoTypeValue_eq f Q A B s, twoTypeValue_half_ge f Q A B,
    fun _ hwA hwB _ hs0 hs1 => three_quarter_le_twoTypeValue f Q A B hwA hwB hs0 hs1⟩

end WindowBounds

end ConsistentSubmodular
