module

public import ConsistentSubmodular.Randomized.Reduction.CheckpointLaw
public import ConsistentSubmodular.Randomized.Reduction.CheckpointAlgorithm

@[expose] public section

/-!
# Lemma 1 and Theorem 2

Lemma 1 (Appendix A.3): an `α`-addition-robust routine yields a randomized
clairvoyant `O(γ⁻²)`-consistent `(α - 3γ)`-approximation. For a small budget,
`k < 8 γ⁻²`, the algorithm recomputes an exact optimum after every arrival. Otherwise
it runs Algorithm 1 with `ℓ = ⌊γk⌋`, `κ = k - 2ℓ`, and `h = ⌈1/γ⌉`; its law is the
pushforward of the independent checkpoint samples and subblock choices. The
consistency bound is `⌈16 γ⁻²⌉ + 3 ≤ 17 γ⁻²`. The last block may be shorter
than `ℓ`; the trajectory ends with the stream, so no dummy arrivals are padded.

Theorem 2 (Appendix A.7) applies Lemma 1 with `α = ξ⋆` and
`γ = min{ε/3, 1/16}`.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

/-! ### Parameters -/

/-- The parameters of Algorithm 1 for the slack `γ` and the budget `k`:
`ℓ = ⌊γk⌋`, `κ = k - 2ℓ`, `h = ⌈1/γ⌉`, and `s = ⌊k/d⌋ + 1 ≥ ⌈k/d⌉` operations per
update, where `d = ⌊ℓ/h⌋` is the minimum subblock length. -/
def params (γ : ℝ) (k : ℕ) : Params where
  ℓ := ⌊γ * k⌋₊
  κ := k - 2 * ⌊γ * k⌋₊
  h := ⌈1 / γ⌉₊
  s := k / (⌊γ * k⌋₊ / ⌈1 / γ⌉₊) + 1

/-- The consistency bound of Lemma 1. -/
def consistency (γ : ℝ) : ℕ := ⌈16 / γ ^ 2⌉₊ + 3

theorem consistency_le {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) :
    (consistency γ : ℝ) ≤ 17 * (1 / γ) ^ 2 := by
  have hinv : 8 < 1 / γ := by rw [lt_one_div (by norm_num) hγ]; linarith
  have hsq : 64 < (1 / γ) ^ 2 := by nlinarith
  have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 16 / γ ^ 2 by positivity)
  have h16 : 16 / γ ^ 2 = 16 * (1 / γ) ^ 2 := by field_simp
  unfold consistency
  push_cast
  linarith

/-- The parameter estimates of the proof of Lemma 1 for `k ≥ 8 γ⁻²`: with
`ℓ ≥ γk/2`, `h ≤ 2/γ`, and `ℓ/h ≥ 2`, the minimum subblock length is
`d = ⌊ℓ/h⌋ ≥ γ²k/8`, so each update needs at most `2⌈k/d⌉ + 1 ≤ 16 γ⁻² + 3`
changes. Moreover `1/h ≤ γ` and `κ/k ≥ 1 - 2γ`. -/
theorem params_spec {γ : ℝ} (hγ : 0 < γ) (hγ8 : γ < 1 / 8) {k : ℕ}
    (hk : 8 / γ ^ 2 ≤ k) :
    (params γ k).Valid k ∧ 2 * (params γ k).s + 1 ≤ consistency γ ∧
      1 / ((params γ k).h : ℝ) ≤ γ ∧ 1 - 2 * γ ≤ ((params γ k).κ : ℝ) / k := by
  have hinv : 8 < 1 / γ := by rw [lt_one_div (by norm_num) hγ]; linarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  have hkγ : 8 ≤ γ ^ 2 * k := by rwa [div_le_iff₀ hγ2, mul_comm] at hk
  have hkpos : (0 : ℝ) < k := by nlinarith
  set x := γ * k with hx
  have hx64 : 64 ≤ x := by
    have : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  -- `ℓ = ⌊γk⌋`
  set ℓ := ⌊x⌋₊ with hℓ
  have hℓle : (ℓ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hℓgt : x < ℓ + 1 := Nat.lt_floor_add_one x
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  -- `h = ⌈1/γ⌉`
  set h := ⌈1 / γ⌉₊ with hh
  have hhge : 1 / γ ≤ h := Nat.le_ceil _
  have hhlt : (h : ℝ) < 1 / γ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hhpos : 0 < h := by
    have : (0 : ℝ) < h := by linarith
    exact_mod_cast this
  have hhγ : (h : ℝ) * γ < 2 := by
    have : (1 / γ + 1) * γ = 1 + γ := by field_simp
    nlinarith
  -- `d = ⌊ℓ/h⌋ ≥ γ²k/8`
  set d := ℓ / h with hd
  have hdiv : ℓ < d * h + h := Nat.lt_div_mul_add hhpos
  have hdivR : (ℓ : ℝ) < (d + 1) * h := by
    have : ((ℓ : ℕ) : ℝ) < ((d * h + h : ℕ) : ℝ) := by exact_mod_cast hdiv
    push_cast at this
    linarith
  have hdγ : γ ^ 2 * k / 8 ≤ d := by
    -- `(d + 1) · 2 > (d + 1) h γ > ℓ γ > γ x / 2`
    have h1 : (ℓ : ℝ) * γ < (d + 1) * (h * γ) := by nlinarith
    have h2 : (d + 1) * (h * γ) ≤ (d + 1) * 2 := by
      apply mul_le_mul_of_nonneg_left hhγ.le
      positivity
    have h3 : x / 2 * γ ≤ ℓ * γ := by nlinarith
    have h4 : x * γ = γ ^ 2 * k := by rw [hx]; ring
    nlinarith
  have hdpos : 0 < d := by
    have : (0 : ℝ) < d := by nlinarith
    exact_mod_cast this
  -- `s = ⌊k/d⌋ + 1`
  have hsd : k ≤ (k / d + 1) * d := by
    have := Nat.lt_div_mul_add (a := k) hdpos
    rw [add_one_mul]
    omega
  have hkd : (k : ℝ) / d ≤ 8 / γ ^ 2 := by
    rw [div_le_div_iff₀ (by exact_mod_cast hdpos) hγ2]
    nlinarith
  have hs : ((k / d : ℕ) : ℝ) ≤ 8 / γ ^ 2 := (Nat.cast_div_le).trans hkd
  have hcons : 2 * (k / d + 1) + 1 ≤ consistency γ := by
    have hc := Nat.le_ceil (16 / γ ^ 2)
    have h16 : 16 / γ ^ 2 = 2 * (8 / γ ^ 2) := by ring
    have : ((2 * (k / d + 1) + 1 : ℕ) : ℝ) ≤ ((consistency γ : ℕ) : ℝ) := by
      unfold consistency
      push_cast
      linarith
    exact_mod_cast this
  -- `2ℓ ≤ k`
  have h2ℓ : 2 * ℓ ≤ k := by
    have : (2 * ℓ : ℝ) ≤ k := by nlinarith
    exact_mod_cast this
  refine ⟨⟨hℓpos, hhpos, ?_, hsd⟩, hcons, ?_, ?_⟩
  · show k - 2 * ℓ + 2 * ℓ ≤ k
    omega
  · show 1 / (h : ℝ) ≤ γ
    rw [div_le_iff₀ (by exact_mod_cast hhpos)]
    have : γ * (1 / γ) = 1 := by field_simp
    nlinarith
  · show 1 - 2 * γ ≤ ((k - 2 * ℓ : ℕ) : ℝ) / k
    rw [Nat.cast_sub h2ℓ, le_div_iff₀ hkpos]
    push_cast
    nlinarith

/-! ### The probability space -/

/-- The random choices of Algorithm 1 on a stream of length `n`: a checkpoint
sample and a subblock for each of the blocks `0, ..., n`. -/
abbrev Sample (n h : ℕ) := (Fin (n + 1) → Finset (Fin n)) × (Fin (n + 1) → Fin h)

/-- The checkpoint samples, indexed by block. -/
def samplesOf {n : ℕ} (a : Fin (n + 1) → Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  if hi : i < n + 1 then a ⟨i, hi⟩ else ∅

/-- The selected subblocks, indexed by block. -/
def choicesOf {n h : ℕ} (b : Fin (n + 1) → Fin h) (i : ℕ) : ℕ :=
  if hi : i < n + 1 then (b ⟨i, hi⟩).val else 0

variable {n : ℕ} {α : ℝ}

/-- The `α`-addition-robust distribution returned at the checkpoint `c`. -/
def robustWeights (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    Finset (Fin n) → ℝ :=
  Classical.choose (hadm n (window f κ c) (window_singleArrivals f κ c))

theorem robustWeights_spec (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    (window f κ c).IsAdditionRobust α (robustWeights hadm f κ c) :=
  Classical.choose_spec (hadm n (window f κ c) (window_singleArrivals f κ c))

/-- The law of the checkpoint sample at `c`. -/
def robustLaw (hadm : AdmitsAdditionRobust α) (f : Objective n) (κ c : ℕ) :
    Law (Finset (Fin n)) where
  weight := robustWeights hadm f κ c
  nonneg := (robustWeights_spec hadm f κ c).1
  sum_one := (robustWeights_spec hadm f κ c).2.1

/-- The law of the random choices: independent checkpoint samples, the one of
block `i` at the checkpoint `τ = iℓ`, and independent uniform subblocks. -/
def sampleLaw (hadm : AdmitsAdditionRobust α) (f : Objective n) (P : Params) (hh : 0 < P.h) :
    Law (Sample n P.h) :=
  (Law.pi fun i : Fin (n + 1) => robustLaw hadm f P.κ (i.val * P.ℓ)).prod
    (Law.pi fun _ : Fin (n + 1) => Law.uniform P.h hh)

theorem good_of_weight (hadm : AdmitsAdditionRobust α) (f : Objective n) (P : Params)
    (hh : 0 < P.h) {ω : Sample n P.h} (hω : (sampleLaw hadm f P hh).weight ω ≠ 0) :
    Good P (samplesOf ω.1) (choicesOf ω.2) := by
  have hA := (Law.weight_prod_ne_zero _ _ hω).1
  intro i
  by_cases hi : i < n + 1
  · have hw := Law.weight_pi_ne_zero _ hA ⟨i, hi⟩
    obtain ⟨hsub, hcard⟩ := (robustWeights_spec hadm f P.κ (i * P.ℓ)).2.2.1 _ hw
    simp only [samplesOf, choicesOf, dif_pos hi]
    exact ⟨(ω.2 ⟨i, hi⟩).isLt, hsub, hcard⟩
  · simp only [samplesOf, choicesOf, dif_neg hi]
    exact ⟨hh, Finset.empty_subset _, by simp⟩

/-! ### The value at a fixed time -/

/-- At most one subblock contains a fixed update strictly inside, so with
probability at least `1 - 1/h` the algorithm holds a full core. -/
theorem subblock_count (ℓ h r : ℕ) (hh : 0 < h) :
    ((h : ℝ) - 1) / h ≤
      (∑ σ : Fin h, ((if r ≤ lo ℓ h σ then 1 else 0) +
        (if ¬ r ≤ lo ℓ h σ ∧ hi ℓ h σ ≤ r then 1 else 0) : ℝ)) / h := by
  have hpoint (σ : Fin h) : ((if r ≤ lo ℓ h σ then 1 else 0) +
      (if ¬ r ≤ lo ℓ h σ ∧ hi ℓ h σ ≤ r then 1 else 0) : ℝ) =
      1 - if lo ℓ h σ < r ∧ r < hi ℓ h σ then 1 else 0 := by
    by_cases h1 : r ≤ lo ℓ h σ
    · have : ¬ (lo ℓ h σ < r ∧ r < hi ℓ h σ) := fun h => by omega
      simp [h1, this]
    · by_cases h2 : hi ℓ h σ ≤ r
      · have : ¬ (lo ℓ h σ < r ∧ r < hi ℓ h σ) := fun h => by omega
        simp [h1, h2, this]
      · have : lo ℓ h σ < r ∧ r < hi ℓ h σ := ⟨by omega, by omega⟩
        simp [h1, h2, this]
  have hcount := card_inside_le_one ℓ h r
  have hsum : (∑ σ : Fin h, (if lo ℓ h σ < r ∧ r < hi ℓ h σ then 1 else 0 : ℝ)) ≤ 1 := by
    rw [Finset.sum_boole]
    exact_mod_cast hcount
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  apply div_le_div_of_nonneg_right _ hhR.le
  rw [Finset.sum_congr rfl fun σ _ => hpoint σ, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

/-- The value at time `u + 1`, as in the proof of Lemma 1: before the selected
subblock the algorithm holds `A_{i-1} ∪ (X_t \ X_{τ_{i-1}})`, after it
`A_i ∪ (X_t \ X_{τ_i})`; in either case the addition-robust guarantee of the
corresponding checkpoint gives `α f(T)` in expectation for every `T ⊆ X_t` with
`|T| ≤ κ`. The selected subblock is independent of the checkpoint samples. -/
theorem expect_run_ge (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hadm : AdmitsAdditionRobust α)
    (f : Objective n) {P : Params} {k : ℕ} (hP : P.Valid k) (u : ℕ) (hu : u + 1 ≤ n)
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (u + 1)) (hTcard : T.card ≤ P.κ) :
    (1 - 1 / (P.h : ℝ)) * (α * f.value T) ≤
      (sampleLaw hadm f P hP.subblocks_pos).expect
        (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u + 1))) := by
  have hℓ := hP.block_pos
  have hh := hP.subblocks_pos
  have hd := Nat.div_add_mod' u P.ℓ
  have hr : u % P.ℓ + 1 ≤ P.ℓ := Nat.mod_lt u hℓ
  set i := u / P.ℓ with hi_def
  set r := u % P.ℓ + 1 with hr_def
  have hit : i * P.ℓ + r = u + 1 := by omega
  have hin : i < n + 1 := by
    have : i ≤ u := Nat.div_le_self u P.ℓ
    omega
  set Z := future n (i * P.ℓ) r with hZ_def
  -- the two options and their indicators
  let Fold : (Fin (n + 1) → Finset (Fin n)) → ℝ :=
    fun a => f.value (oldCore n P.ℓ (samplesOf a) i ∪ Z)
  let Fnew : (Fin (n + 1) → Finset (Fin n)) → ℝ := fun a => f.value (samplesOf a i ∪ Z)
  let G1 : (Fin (n + 1) → Fin P.h) → ℝ :=
    fun b => if r ≤ lo P.ℓ P.h (choicesOf b i) then 1 else 0
  let G2 : (Fin (n + 1) → Fin P.h) → ℝ :=
    fun b => if ¬ r ≤ lo P.ℓ P.h (choicesOf b i) ∧ hi P.ℓ P.h (choicesOf b i) ≤ r then 1 else 0
  set μA := Law.pi fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ) with hμA
  set μσ := Law.pi fun _ : Fin (n + 1) => Law.uniform P.h hh with hμσ
  -- pointwise lower bound for choices of positive probability
  have hpoint : (sampleLaw hadm f P hh).expect (fun ω => Fold ω.1 * G1 ω.2 + Fnew ω.1 * G2 ω.2) ≤
      (sampleLaw hadm f P hh).expect
        (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u + 1))) := by
    apply Law.expect_mono
    intro ω hω
    have hg := good_of_weight hadm f P hh hω
    have hv := value_le_run hP hg f u
    simp only [Fold, Fnew, G1, G2]
    split_ifs at hv ⊢ <;> linarith
  -- independence: the expectation factorizes
  have hsplit : (sampleLaw hadm f P hh).expect (fun ω => Fold ω.1 * G1 ω.2 + Fnew ω.1 * G2 ω.2) =
      μA.expect Fold * μσ.expect G1 + μA.expect Fnew * μσ.expect G2 := by
    rw [sampleLaw, Law.expect_add, Law.expect_prod_mul, Law.expect_prod_mul]
  -- the subblock probabilities
  have hG : μσ.expect G1 + μσ.expect G2 ≥ 1 - 1 / (P.h : ℝ) := by
    have h1 : μσ.expect G1 = (∑ σ : Fin P.h, (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ)) / P.h := by
      have : G1 = fun b => (fun σ : Fin P.h => (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ))
          (b ⟨i, hin⟩) := by
        funext b
        simp only [G1, choicesOf, dif_pos hin]
      rw [this, hμσ]
      exact (Law.expect_pi_apply (fun _ : Fin (n + 1) => Law.uniform P.h hh) ⟨i, hin⟩
        (fun σ : Fin P.h => (if r ≤ lo P.ℓ P.h σ then 1 else 0 : ℝ))).trans
        (Law.expect_uniform _ _ _)
    have h2 : μσ.expect G2 = (∑ σ : Fin P.h,
        (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ)) / P.h := by
      have : G2 = fun b => (fun σ : Fin P.h =>
          (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ)) (b ⟨i, hin⟩) := by
        funext b
        simp only [G2, choicesOf, dif_pos hin]
      rw [this, hμσ]
      exact (Law.expect_pi_apply (fun _ : Fin (n + 1) => Law.uniform P.h hh) ⟨i, hin⟩
        (fun σ : Fin P.h =>
          (if ¬ r ≤ lo P.ℓ P.h σ ∧ hi P.ℓ P.h σ ≤ r then 1 else 0 : ℝ))).trans
        (Law.expect_uniform _ _ _)
    have hc := subblock_count P.ℓ P.h r hh
    rw [h1, h2, ← add_div, ← Finset.sum_add_distrib]
    have hhR : (0 : ℝ) < P.h := by exact_mod_cast hh
    have : ((P.h : ℝ) - 1) / P.h = 1 - 1 / P.h := by field_simp
    linarith
  -- the new core: the addition-robust guarantee at the checkpoint `iℓ`
  have hnew : α * f.value T ≤ μA.expect Fnew := by
    have : Fnew = fun a => (fun S => f.value (S ∪ Z)) (a ⟨i, hin⟩) := by
      funext a
      simp only [Fnew, samplesOf, dif_pos hin]
    rw [this, hμA]
    refine le_of_le_of_eq ?_ (Law.expect_pi_apply
      (fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ)) ⟨i, hin⟩
      (fun S => f.value (S ∪ Z))).symm
    exact robust_le hα0 (robustWeights_spec hadm f P.κ (i * P.ℓ)) (by omega)
      (by rw [hit]; exact hT) hTcard
  -- the old core: the guarantee at the checkpoint `(i - 1)ℓ`, or all arrivals
  have hold : α * f.value T ≤ μA.expect Fold := by
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · have : Fold = fun _ => f.value Z := by
        funext a
        simp only [Fold, oldCore, if_pos hi0, Finset.empty_union]
      rw [this, Law.expect_const]
      have hZ : T ⊆ Z := by
        intro e he
        have := hT he
        have hi0' : i * P.ℓ = 0 := by rw [hi0, zero_mul]
        rw [hZ_def, hi0']
        simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and]
          at this ⊢
        omega
      have hmono := f.monotone _ _ hZ
      have hfT := f.nonnegative T
      nlinarith
    · obtain ⟨j, hj⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hjn : j < n + 1 := by omega
      have hjℓ : j * P.ℓ + P.ℓ = i * P.ℓ := by rw [hj]; ring
      have : Fold = fun a => (fun S => f.value (S ∪ future n (j * P.ℓ) (P.ℓ + r)))
          (a ⟨j, hjn⟩) := by
        funext a
        simp only [Fold, oldCore, if_neg (Nat.pos_iff_ne_zero.mp hi0), samplesOf]
        rw [show i - 1 = j by omega, dif_pos hjn, Finset.union_assoc, block, hZ_def, ← hjℓ,
          block_union_future _ _ _ hr]
      rw [this, hμA]
      refine le_of_le_of_eq ?_ (Law.expect_pi_apply
        (fun j : Fin (n + 1) => robustLaw hadm f P.κ (j.val * P.ℓ)) ⟨j, hjn⟩
        (fun S => f.value (S ∪ future n (j * P.ℓ) (P.ℓ + r)))).symm
      exact robust_le hα0 (robustWeights_spec hadm f P.κ (j * P.ℓ)) (by omega)
        (by rw [show j * P.ℓ + (P.ℓ + r) = u + 1 by omega]; exact hT) hTcard
  have hG1 : 0 ≤ μσ.expect G1 := Law.expect_nonneg _ fun b => by
    simp only [G1]; split_ifs <;> norm_num
  have hG2 : 0 ≤ μσ.expect G2 := Law.expect_nonneg _ fun b => by
    simp only [G2]; split_ifs <;> norm_num
  have hαT : 0 ≤ α * f.value T := mul_nonneg hα0 (f.nonnegative T)
  calc (1 - 1 / (P.h : ℝ)) * (α * f.value T)
      ≤ (μσ.expect G1 + μσ.expect G2) * (α * f.value T) :=
        mul_le_mul_of_nonneg_right hG hαT
    _ = μσ.expect G1 * (α * f.value T) + μσ.expect G2 * (α * f.value T) := by ring
    _ ≤ μσ.expect G1 * μA.expect Fold + μσ.expect G2 * μA.expect Fnew :=
        add_le_add (mul_le_mul_of_nonneg_left hold hG1) (mul_le_mul_of_nonneg_left hnew hG2)
    _ = μA.expect Fold * μσ.expect G1 + μA.expect Fnew * μσ.expect G2 := by ring
    _ ≤ _ := by rw [← hsplit]; exact hpoint

/-! ### Lemma 1 -/

theorem feasible_mono {n k C C' : ℕ} {S : Fin (n + 1) → Finset (Fin n)}
    (hS : FeasibleTrajectory k C S) (hC : C ≤ C') : FeasibleTrajectory k C' S :=
  ⟨hS.1, hS.2.1, fun t => (hS.2.2 t).trans hC⟩

/-- Small budgets: recompute an exact optimum after every arrival. -/
def optimum (f : Objective n) (k t : ℕ) : Finset (Fin n) :=
  optimalCore f (arrivedPrefix n t) ∅ k

theorem feasible_optimum (f : Objective n) (k : ℕ) :
    FeasibleTrajectory k (2 * k) (fun t : Fin (n + 1) => optimum f k t.val) := by
  obtain ⟨hsub0, -, -⟩ := optimalCore_spec f (arrivedPrefix n 0) ∅ k
  refine ⟨?_, fun t => ?_, fun t => ?_⟩
  · apply Finset.subset_empty.mp
    intro e he
    have := hsub0 he
    simp [arrivedPrefix] at this
  · exact ⟨(optimalCore_spec _ _ _ _).1, (optimalCore_spec _ _ _ _).2.1⟩
  · unfold recourse
    have h1 := (optimalCore_spec f (arrivedPrefix n (t.val + 1)) ∅ k).2.1
    have h2 := (optimalCore_spec f (arrivedPrefix n t.val) ∅ k).2.1
    have h3 := Finset.card_union_le (optimum f k (t.val + 1) \ optimum f k t.val)
      (optimum f k t.val \ optimum f k (t.val + 1))
    have h4 := Finset.card_le_card (Finset.sdiff_subset (s := optimum f k (t.val + 1))
      (t := optimum f k t.val))
    have h5 := Finset.card_le_card (Finset.sdiff_subset (s := optimum f k t.val)
      (t := optimum f k (t.val + 1)))
    simp only [Fin.val_succ, Fin.val_castSucc]
    unfold optimum at *
    omega

theorem le_optimum (f : Objective n) {k t : ℕ} {A : Finset (Fin n)}
    (hA : A ⊆ arrivedPrefix n t) (hAk : A.card ≤ k) : f.value A ≤ f.value (optimum f k t) := by
  have h := (optimalCore_spec f (arrivedPrefix n t) ∅ k).2.2 A hA hAk
  simpa [optimum] using h

/-- **Lemma 1** (from clairvoyant addition robustness to consistency). An
`α`-addition-robust routine gives, for every `γ ∈ (0, 1/8)`, a randomized
clairvoyant algorithm that is `(⌈16 γ⁻²⌉ + 3)`-consistent, at most `17 γ⁻²`, and an
`(α - 3γ)`-approximation. -/
theorem additionRobustReduction : AdditionRobustReductionGoal := by
  refine ⟨17, fun γ hγ hγ8 => ⟨consistency γ, consistency_le hγ hγ8,
    fun α hα0 hα1 hadm n k f => ?_⟩⟩
  by_cases hk : 8 / γ ^ 2 ≤ (k : ℝ)
  · -- Algorithm 1
    obtain ⟨hP, hcons, hh, hκ⟩ := params_spec hγ hγ8 hk
    set P := params γ k
    let τ : Sample n P.h → Fin (n + 1) → Finset (Fin n) :=
      fun ω t => run P (samplesOf ω.1) (choicesOf ω.2) t.val
    refine ⟨(sampleLaw hadm f P hP.subblocks_pos).trajectory τ, ?_, fun t A hA hAk => ?_⟩
    · apply Law.feasible_trajectory
      intro ω hω
      exact feasible_mono (feasible_run hP (good_of_weight hadm f P hP.subblocks_pos hω)) hcons
    · rw [Law.expectation_trajectory]
      have hγ2 : 0 < γ ^ 2 := by positivity
      have hkpos : 0 < k := by
        have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk
        exact_mod_cast this
      have hfA := f.nonnegative A
      obtain ⟨u, rfl⟩ | ht0 : (∃ u : Fin n, t = u.succ) ∨ t = 0 := by
        rcases Fin.eq_zero_or_eq_succ t with h0 | ⟨u, hu⟩
        · exact Or.inr h0
        · exact Or.inl ⟨u, hu⟩
      · -- a time after an arrival
        have hκk : P.κ ≤ k := by have := hP.budget; omega
        obtain ⟨T, hTA, hTcard, hTval⟩ := exists_subset_fraction f hAk hκk hkpos
        have hT : T ⊆ arrivedPrefix n (u.val + 1) := hTA.trans (by simpa using hA)
        have hE := expect_run_ge hα0 hα1 hadm f hP u.val (by omega) hT hTcard
        show (α - 3 * γ) * f.value A ≤ (sampleLaw hadm f P hP.subblocks_pos).expect
          (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) (u.val + 1)))
        have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
        have hγ' : γ < 1 := by linarith
        have h1 : 1 - γ ≤ 1 - 1 / (P.h : ℝ) := by linarith
        have h1' : 0 ≤ 1 - γ := by linarith
        have h2' : 0 ≤ 1 - 2 * γ := by linarith
        have hfrac : (1 - γ) * (1 - 2 * γ) ≤ (1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k) :=
          mul_le_mul h1 hκ h2' (by linarith)
        have hfT := f.nonnegative T
        -- `(α - 3γ) f(A) ≤ (1 - 3γ) α f(A) ≤ (1 - 1/h) (κ/k) α f(A) ≤ (1 - 1/h) α f(T)`
        have hstep1 : (α - 3 * γ) * f.value A ≤ ((1 - γ) * (1 - 2 * γ)) * (α * f.value A) := by
          have : (α - 3 * γ) ≤ ((1 - γ) * (1 - 2 * γ)) * α := by nlinarith
          nlinarith
        have hstep2 : ((1 - γ) * (1 - 2 * γ)) * (α * f.value A) ≤
            ((1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k)) * (α * f.value A) :=
          mul_le_mul_of_nonneg_right hfrac (mul_nonneg hα0 hfA)
        have hstep3 : ((1 - 1 / (P.h : ℝ)) * ((P.κ : ℝ) / k)) * (α * f.value A) ≤
            (1 - 1 / (P.h : ℝ)) * (α * f.value T) := by
          have h3 : 0 ≤ (1 - 1 / (P.h : ℝ)) * α := mul_nonneg (by linarith) hα0
          have := mul_le_mul_of_nonneg_left hTval h3
          linarith
        linarith
      · -- time zero
        subst ht0
        have hA0 : A = ∅ := by
          apply Finset.subset_empty.mp
          intro e he
          have := hA he
          simp [arrivedPrefix] at this
        subst hA0
        have hrun (ω : Sample n P.h) : run P (samplesOf ω.1) (choicesOf ω.2) 0 = ∅ := by
          have := state_zero (P := P) (A := samplesOf ω.1) (σ := choicesOf ω.2) 0
          simp only [run, phase, pos, Nat.zero_sub, Nat.zero_div, zero_mul] at this ⊢
          rw [this]
          simp [oldCore]
        show (α - 3 * γ) * f.value ∅ ≤ (sampleLaw hadm f P hP.subblocks_pos).expect
          (fun ω => f.value (run P (samplesOf ω.1) (choicesOf ω.2) 0))
        simp only [hrun, Law.expect_const]
        have h0 := f.nonnegative ∅
        nlinarith
  · -- small budgets: an exact optimum after every arrival
    have hk' : (k : ℝ) < 8 / γ ^ 2 := lt_of_not_ge hk
    have hrec : 2 * k ≤ consistency γ := by
      have hc := Nat.le_ceil (16 / γ ^ 2)
      have : ((2 * k : ℕ) : ℝ) ≤ ((consistency γ : ℕ) : ℝ) := by
        unfold consistency
        push_cast
        have : 16 / γ ^ 2 = 2 * (8 / γ ^ 2) := by ring
        linarith
      exact_mod_cast this
    refine ⟨(Law.dirac ()).trajectory (fun _ t => optimum f k t.val), ?_, fun t A hA hAk => ?_⟩
    · exact Law.feasible_trajectory _ _ fun _ _ => feasible_mono (feasible_optimum f k) hrec
    · rw [Law.expectation_trajectory, Law.expect_dirac]
      have hle := le_optimum f hA hAk
      have hfA := f.nonnegative A
      nlinarith

/-! ### Theorem 2 -/

/-- **Theorem 2** (Appendix A.7), from Lemma 1 and a `ξ⋆`-addition-robust
routine: apply Lemma 1 with `γ = min{ε/3, 1/16}`. The approximation is at least
`ξ⋆ - ε`, and since `1/γ ≤ 16/ε` the consistency is at most `256 K ε⁻²`. -/
theorem randomizedLower_of (hred : AdditionRobustReductionGoal) (hξ0 : 0 ≤ xiStar)
    (hξ1 : xiStar ≤ 1) (hrobust : AdmitsAdditionRobust xiStar) : RandomizedLowerGoal := by
  obtain ⟨K, hK⟩ := hred
  refine ⟨256 * max K 0, fun ε hε hε1 => ?_⟩
  set γ := min (ε / 3) (1 / 16) with hγ_def
  have hγ : 0 < γ := lt_min (by positivity) (by norm_num)
  have hγ8 : γ < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hγε : 3 * γ ≤ ε := by
    have := min_le_left (ε / 3) (1 / 16)
    linarith
  obtain ⟨C, hC, hG⟩ := hK γ hγ hγ8
  refine ⟨C, ?_, fun n k f => ?_⟩
  · have hinv : 1 / γ ≤ 16 / ε := by
      rw [div_le_div_iff₀ hγ hε]
      rcases min_choice (ε / 3) (1 / 16) with h | h
      · rw [← hγ_def] at h
        rw [h]
        linarith
      · rw [← hγ_def] at h
        rw [h]
        linarith
    have hsq : (1 / γ) ^ 2 ≤ 256 * (1 / ε) ^ 2 := by
      have h0 : 0 ≤ 1 / γ := by positivity
      have : (16 / ε) ^ 2 = 256 * (1 / ε) ^ 2 := by ring
      nlinarith
    have hK0 : K ≤ max K 0 := le_max_left K 0
    have hm : 0 ≤ max K 0 := le_max_right K 0
    calc (C : ℝ) ≤ K * (1 / γ) ^ 2 := hC
      _ ≤ max K 0 * (1 / γ) ^ 2 := mul_le_mul_of_nonneg_right hK0 (by positivity)
      _ ≤ max K 0 * (256 * (1 / ε) ^ 2) := mul_le_mul_of_nonneg_left hsq hm
      _ = 256 * max K 0 * (1 / ε) ^ 2 := by ring
  · obtain ⟨μ, hμ, hval⟩ := hG xiStar hξ0 hξ1 hrobust n k f
    refine ⟨μ, hμ, fun t A hA hAk => ?_⟩
    have h := hval t A hA hAk
    have hfA := f.nonnegative A
    nlinarith

end ConsistentSubmodular.Checkpoints
