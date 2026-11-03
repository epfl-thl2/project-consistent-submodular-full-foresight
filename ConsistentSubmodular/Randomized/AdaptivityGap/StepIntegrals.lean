module

public import ConsistentSubmodular.Randomized.AdaptivityGap.ShadowChains

@[expose] public section

/-!
# The step functions of the proof of Lemma 3

The analytic part of the proof of Lemma 3 (Appendix A.5). A random left endpoint `ℓ_J` has the
distribution function `W(x) = Pr[ℓ_J ≤ x]`, a nondecreasing step function. Its integral
`H(x) = ∫^x W = Σ_j p_j (x - ℓ_j)⁺` is piecewise linear and strictly increasing beyond the
smallest left endpoint of positive probability, with inverse `X = H⁻¹` and
`g(y) = 1 / W(X(y))`. Here `X' = g` from the right, so `X(b) - X(a) = ∫_a^b g`, and
`Pr[H(ℓ_J) ≤ y] = 1 / g(y)`. These give identities (10) and (11), and averaging the
consecutive chains `g(s), g(s + 1), …` over `s ∈ [0, 1]` proves inequality (7) for intervals
with `∫_{ℓ_i}^{r_i} W ≤ 1`.

The paper first translates the left endpoints so that their minimum is `0`. Here the minimum
`low` is kept; it only adds the slack `(1 - α) low ≥ 0` at the end, as in the paper.
-/

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

/-- A bounded measurable function is integrable on every bounded interval. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- Averaging translates over `s ∈ [0, 1]`: `∫_0^1 Σ_{j<N} φ(s + j) ds = ∫_0^N φ`. -/
theorem integral_sum_shift {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (N : ℕ) : ∫ s in (0 : ℝ)..1, ∑ j ∈ Finset.range N, φ (s + j) = ∫ y in (0 : ℝ)..N, φ y := by
  rw [intervalIntegral.integral_finset_sum (s := Finset.range N)
    (f := fun (j : ℕ) (s : ℝ) => φ (s + j)) fun j _ =>
      intervalIntegrable_of_bounded (f := fun s : ℝ => φ (s + j))
        (hφ.comp (measurable_add_const _)) (fun x => hC _) 0 1]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ)
    (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ => intervalIntegrable_of_bounded hφ hC _ _
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_comp_add_right]
  push_cast
  ring_nf

/-- The law of the random left endpoint `ℓ_J`: weights `prob` on the left endpoints `left`,
whose support has smallest point `low`. -/
structure LeftLaw (ι : Type*) [Fintype ι] where
  prob : ι → ℝ
  left : ι → ℝ
  low : ℝ
  prob_nonneg : ∀ j, 0 ≤ prob j
  prob_sum : ∑ j, prob j = 1
  low_le : ∀ j, prob j ≠ 0 → low ≤ left j
  atom : ∃ j, prob j ≠ 0 ∧ left j ≤ low

namespace LeftLaw

variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

/-- The distribution function `W(x) = Pr[ℓ_J ≤ x]`. -/
def cdf (x : ℝ) : ℝ := ∑ j, if L.left j ≤ x then L.prob j else 0

/-- `H(x) = Σ_j p_j (x - ℓ_j)⁺ = ∫_{low}^x W`. -/
def ramp (x : ℝ) : ℝ := ∑ j, L.prob j * max 0 (x - L.left j)

/-- The mean left endpoint `B = E[ℓ_J]`. -/
def mean : ℝ := ∑ j, L.prob j * L.left j

/-- The inverse `X = H⁻¹ : [0, ∞) → [low, ∞)`, extended by `X(0)` to negative arguments. -/
def inv (y : ℝ) : ℝ := Function.invFunOn L.ramp (Ici L.low) (max y 0)

/-- `g(y) = 1 / W(X(y))`. -/
def slope (y : ℝ) : ℝ := 1 / L.cdf (L.inv y)

theorem cdf_nonneg (x : ℝ) : 0 ≤ L.cdf x :=
  Finset.sum_nonneg fun j _ => by split_ifs; exacts [L.prob_nonneg j, le_rfl]

theorem cdf_le_one (x : ℝ) : L.cdf x ≤ 1 := by
  rw [← L.prob_sum]
  exact Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, L.prob_nonneg j]

theorem cdf_mono : Monotone L.cdf := fun x y hxy => Finset.sum_le_sum fun j _ => by
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h1.trans hxy) h2
  · exact L.prob_nonneg j
  · exact le_rfl

theorem cdf_low_pos : 0 < L.cdf L.low := by
  obtain ⟨j, hj, hjl⟩ := L.atom
  calc 0 < L.prob j := lt_of_le_of_ne (L.prob_nonneg j) (Ne.symm hj)
    _ = if L.left j ≤ L.low then L.prob j else 0 := (if_pos hjl).symm
    _ ≤ L.cdf L.low := Finset.single_le_sum
        (f := fun j => if L.left j ≤ L.low then L.prob j else 0)
        (fun i _ => by dsimp only; split_ifs; exacts [L.prob_nonneg i, le_rfl])
        (Finset.mem_univ j)

theorem cdf_pos {x : ℝ} (hx : L.low ≤ x) : 0 < L.cdf x :=
  L.cdf_low_pos.trans_le (L.cdf_mono hx)

theorem cdf_eq_one {x : ℝ} (hx : ∀ j, L.left j ≤ x) : L.cdf x = 1 := by
  rw [← L.prob_sum]
  exact Finset.sum_congr rfl fun j _ => if_pos (hx j)

theorem ramp_nonneg (x : ℝ) : 0 ≤ L.ramp x :=
  Finset.sum_nonneg fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)

theorem pos_part_sub {a b c : ℝ} (hab : a ≤ b) :
    max 0 (b - c) - max 0 (a - c) = max 0 (b - max a c) := by
  simp only [max_def]
  split_ifs <;> linarith

/-- Fubini (8): `Σ_j p_j |[a, b] ∩ [ℓ_j, ∞)| = H(b) - H(a)`. -/
theorem ramp_sub {a b : ℝ} (hab : a ≤ b) :
    L.ramp b - L.ramp a = ∑ j, L.prob j * max 0 (b - max a (L.left j)) := by
  rw [ramp, ramp, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← mul_sub, pos_part_sub hab]

theorem ramp_mono : Monotone L.ramp := fun a b hab => by
  have h := L.ramp_sub hab
  have : 0 ≤ ∑ j, L.prob j * max 0 (b - max a (L.left j)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)
  linarith

theorem ramp_low : L.ramp L.low = 0 := Finset.sum_eq_zero fun j _ => by
  by_cases h : L.prob j = 0
  · simp [h]
  · rw [max_eq_left (by linarith [L.low_le j h]), mul_zero]

theorem ramp_sub_ge {a b : ℝ} (hab : a ≤ b) : L.cdf a * (b - a) ≤ L.ramp b - L.ramp a := by
  rw [L.ramp_sub hab, cdf, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · rw [max_eq_left h, max_eq_right (sub_nonneg.mpr hab)]
  · rw [zero_mul]
    exact mul_nonneg (L.prob_nonneg j) (le_max_left _ _)

theorem ramp_strictMonoOn : StrictMonoOn L.ramp (Ici L.low) := by
  intro a ha b _ hab
  have h := L.ramp_sub_ge hab.le
  have hc := L.cdf_pos ha
  nlinarith [mul_pos hc (sub_pos.mpr hab)]

theorem ramp_continuous : Continuous L.ramp :=
  continuous_finset_sum _ fun _ _ =>
    continuous_const.mul (continuous_const.max (continuous_id.sub continuous_const))

/-- Beyond every left endpoint, `H(x) = x - B`. -/
theorem ramp_of_ge {x : ℝ} (hx : ∀ j, L.left j ≤ x) : L.ramp x = x - L.mean := by
  rw [ramp, mean]
  calc ∑ j, L.prob j * max 0 (x - L.left j) = ∑ j, (L.prob j * x - L.prob j * L.left j) :=
        Finset.sum_congr rfl fun j _ => by rw [max_eq_right (sub_nonneg.mpr (hx j))]; ring
    _ = x - ∑ j, L.prob j * L.left j := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, L.prob_sum, one_mul]

/-- `H` maps `[low, ∞)` onto `[0, ∞)`. -/
theorem exists_ramp_eq {y : ℝ} (hy : 0 ≤ y) : ∃ x ∈ Ici L.low, L.ramp x = y := by
  have hc := L.cdf_low_pos
  have hle : L.low ≤ L.low + y / L.cdf L.low := le_add_of_nonneg_right (div_nonneg hy hc.le)
  have hhigh : y ≤ L.ramp (L.low + y / L.cdf L.low) := by
    have h := L.ramp_sub_ge hle
    rwa [L.ramp_low, sub_zero, add_sub_cancel_left, mul_div_cancel₀ _ hc.ne'] at h
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hle L.ramp_continuous.continuousOn
    ⟨by rw [L.ramp_low]; exact hy, hhigh⟩
  exact ⟨x, hx.1, hxy⟩

theorem inv_spec (y : ℝ) : L.inv y ∈ Ici L.low ∧ L.ramp (L.inv y) = max y 0 :=
  Function.invFunOn_pos (L.exists_ramp_eq (le_max_right y 0))

theorem low_le_inv (y : ℝ) : L.low ≤ L.inv y := (L.inv_spec y).1

theorem ramp_inv {y : ℝ} (hy : 0 ≤ y) : L.ramp (L.inv y) = y := by
  rw [(L.inv_spec y).2, max_eq_left hy]

theorem inv_ramp {x : ℝ} (hx : L.low ≤ x) : L.inv (L.ramp x) = x :=
  L.ramp_strictMonoOn.injOn (L.low_le_inv _) hx (L.ramp_inv (L.ramp_nonneg x))

theorem inv_zero : L.inv 0 = L.low := by
  rw [← L.ramp_low, L.inv_ramp le_rfl]

theorem inv_mono : Monotone L.inv := by
  intro y y' h
  by_contra hlt
  have := L.ramp_strictMonoOn (L.low_le_inv y') (L.low_le_inv y) (lt_of_not_ge hlt)
  rw [(L.inv_spec y).2, (L.inv_spec y').2] at this
  exact absurd (max_le_max h le_rfl) (not_le.mpr this)

/-- `X` is Lipschitz with constant `1 / W(low)`. -/
theorem inv_sub_le {y y' : ℝ} (h : y ≤ y') :
    L.inv y' - L.inv y ≤ (y' - y) / L.cdf L.low := by
  have hle := L.inv_mono h
  have h1 := L.ramp_sub_ge hle
  rw [(L.inv_spec y).2, (L.inv_spec y').2] at h1
  have h2 : max y' 0 - max y 0 ≤ y' - y := by
    simp only [max_def]
    split_ifs <;> linarith
  have h3 := mul_le_mul_of_nonneg_right (L.cdf_mono (L.low_le_inv y)) (sub_nonneg.mpr hle)
  rw [le_div_iff₀ L.cdf_low_pos]
  nlinarith

theorem inv_continuous : Continuous L.inv := by
  have hc := L.cdf_low_pos
  refine (LipschitzWith.of_dist_le_mul (K := ⟨1 / L.cdf L.low, (one_div_pos.mpr hc).le⟩)
    fun y y' => ?_).continuous
  simp only [Real.dist_eq]
  rcases le_total y y' with h | h
  · have h1 := L.inv_sub_le h
    have h2 := L.inv_mono h
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h2), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h)]
    calc L.inv y' - L.inv y ≤ (y' - y) / L.cdf L.low := h1
      _ = 1 / L.cdf L.low * (y' - y) := by ring
  · have h1 := L.inv_sub_le h
    have h2 := L.inv_mono h
    rw [abs_of_nonneg (sub_nonneg.mpr h2), abs_of_nonneg (sub_nonneg.mpr h)]
    calc L.inv y - L.inv y' ≤ (y - y') / L.cdf L.low := h1
      _ = 1 / L.cdf L.low * (y - y') := by ring

/-- `H` is linear with slope `W(x)` just to the right of `x`. -/
theorem ramp_right (x : ℝ) : ∀ᶠ h in 𝓝[≥] (0 : ℝ), L.ramp (x + h) = L.ramp x + L.cdf x * h := by
  have key : ∀ j, ∀ᶠ h in 𝓝[≥] (0 : ℝ), max 0 (x + h - L.left j) =
      max 0 (x - L.left j) + (if L.left j ≤ x then h else 0) := by
    intro j
    by_cases hj : L.left j ≤ x
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 ≤ h)
      rw [if_pos hj, max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [not_le] at hj
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr hj))] with h
        (hh : h < L.left j - x)
      rw [if_neg (not_le.mpr hj), max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
  filter_upwards [Filter.eventually_all.2 key] with h hh
  simp only [ramp, cdf, hh, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

/-- `X` is linear with slope `g(y)` just to the right of `y ≥ 0`. -/
theorem inv_right {y : ℝ} (hy : 0 ≤ y) :
    ∀ᶠ t in 𝓝[≥] y, L.inv t = L.inv y + (t - y) * L.slope y := by
  have hc : 0 < L.cdf (L.inv y) := L.cdf_pos (L.low_le_inv y)
  have htend : Tendsto (fun t => (t - y) / L.cdf (L.inv y)) (𝓝[≥] y) (𝓝[≥] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (((continuous_id.sub continuous_const).div_const _).tendsto' y 0
        (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : y ≤ t)
      exact div_nonneg (sub_nonneg.mpr ht) hc.le
  filter_upwards [htend.eventually (L.ramp_right (L.inv y)), self_mem_nhdsWithin] with t ht
    (hyt : y ≤ t)
  have hx' : L.low ≤ L.inv y + (t - y) / L.cdf (L.inv y) :=
    le_add_of_le_of_nonneg (L.low_le_inv y) (div_nonneg (sub_nonneg.mpr hyt) hc.le)
  have hramp : L.ramp (L.inv y + (t - y) / L.cdf (L.inv y)) = t := by
    rw [ht, L.ramp_inv hy, mul_div_cancel₀ _ hc.ne']
    ring
  calc L.inv t = L.inv (L.ramp (L.inv y + (t - y) / L.cdf (L.inv y))) := by rw [hramp]
    _ = L.inv y + (t - y) / L.cdf (L.inv y) := L.inv_ramp hx'
    _ = L.inv y + (t - y) * L.slope y := by rw [slope, mul_one_div]

theorem hasDerivWithinAt_inv {y : ℝ} (hy : 0 ≤ y) :
    HasDerivWithinAt L.inv (L.slope y) (Ioi y) y := by
  have haff : HasDerivAt (fun t => L.inv y + (t - y) * L.slope y) (L.slope y) y := by
    simpa using (((hasDerivAt_id y).sub_const y).mul_const (L.slope y)).const_add (L.inv y)
  exact (haff.hasDerivWithinAt.congr_of_eventuallyEq (L.inv_right hy) (by simp)).mono
    Ioi_subset_Ici_self

theorem slope_antitone : Antitone L.slope := fun _ _ h =>
  one_div_le_one_div_of_le (L.cdf_pos (L.low_le_inv _)) (L.cdf_mono (L.inv_mono h))

theorem one_le_slope (y : ℝ) : 1 ≤ L.slope y := by
  rw [slope, le_div_iff₀ (L.cdf_pos (L.low_le_inv y)), one_mul]
  exact L.cdf_le_one _

theorem slope_le (y : ℝ) : L.slope y ≤ 1 / L.cdf L.low :=
  one_div_le_one_div_of_le L.cdf_low_pos (L.cdf_mono (L.low_le_inv y))

theorem slope_measurable : Measurable L.slope := L.slope_antitone.measurable

theorem abs_slope_le (y : ℝ) : |L.slope y| ≤ 1 / L.cdf L.low := by
  rw [abs_of_nonneg (zero_le_one.trans (L.one_le_slope y))]
  exact L.slope_le y

/-- `X(b) - X(a) = ∫_a^b g` for `0 ≤ a ≤ b`. -/
theorem integral_slope {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ y in a..b, L.slope y = L.inv b - L.inv a :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab L.inv_continuous.continuousOn
    (fun _ hy => L.hasDerivWithinAt_inv (ha.trans hy.1.le))
    (intervalIntegrable_of_bounded L.slope_measurable L.abs_slope_le a b)

/-- `Pr[H(ℓ_J) ≤ y] = W(X(y)) = 1 / g(y)` for `y ≥ 0`. -/
theorem cdf_inv {y : ℝ} (hy : 0 ≤ y) :
    L.cdf (L.inv y) = ∑ j, if L.ramp (L.left j) ≤ y then L.prob j else 0 := by
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hp : L.prob j = 0
  · simp [hp]
  · have h2 := L.ramp_strictMonoOn.le_iff_le (L.low_le j hp) (L.low_le_inv y)
    rw [L.ramp_inv hy] at h2
    simp only [h2]

/-- The part of `∫ g(y + 1) Pr[S ≤ y] dy` contributed by a realization `S = H(ℓ_j)`. -/
theorem integral_slope_after {S Y : ℝ} (hS : 0 ≤ S) (hSY : S ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * (if S ≤ y then 1 else 0) =
      L.inv (Y + 1) - L.inv (S + 1) := by
  have hmeas : Measurable fun y : ℝ => L.slope (y + 1) * (if S ≤ y then (1 : ℝ) else 0) :=
    (L.slope_measurable.comp (measurable_add_const 1)).mul
      (Measurable.ite measurableSet_Ici measurable_const measurable_const)
  have hbound : ∀ y, |L.slope (y + 1) * (if S ≤ y then (1 : ℝ) else 0)| ≤ 1 / L.cdf L.low := by
    intro y
    split_ifs
    · rw [mul_one]; exact L.abs_slope_le _
    · rw [mul_zero, abs_zero]; exact (one_div_pos.mpr L.cdf_low_pos).le
  have hint := intervalIntegrable_of_bounded hmeas hbound
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 S) (hint S Y)]
  have h1 : ∫ y in (0 : ℝ)..S, L.slope (y + 1) * (if S ≤ y then 1 else 0) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) ?_,
      intervalIntegral.integral_zero]
    filter_upwards [(Set.countable_singleton S).ae_notMem volume] with y hy hmem
    rw [Set.uIoc_of_le hS] at hmem
    have hlt : y < S := lt_of_le_of_ne hmem.2 (by simpa using hy)
    simp [not_le.mpr hlt]
  have h2 : ∫ y in S..Y, L.slope (y + 1) * (if S ≤ y then 1 else 0) =
      ∫ y in S..Y, L.slope (y + 1) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [Set.uIcc_of_le hSY] at hy
    simp [hy.1]
  rw [h1, h2, zero_add, intervalIntegral.integral_comp_add_right,
    L.integral_slope (by linarith) (by linarith)]

/-- Fubini: `∫_0^Y g(y + 1) Pr[S ≤ y] dy = Σ_j p_j (X(Y + 1) - X(S_j + 1))`, where
`S_j = H(ℓ_j)`. -/
theorem integral_slope_mul_cdf {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * L.cdf (L.inv y) =
      ∑ j, L.prob j * (L.inv (Y + 1) - L.inv (L.ramp (L.left j) + 1)) := by
  have hcongr : Set.EqOn (fun y => L.slope (y + 1) * L.cdf (L.inv y))
      (fun y => ∑ j, L.prob j * (L.slope (y + 1) *
        (if L.ramp (L.left j) ≤ y then 1 else 0))) (Set.uIcc 0 Y) := by
    intro y hy
    rw [Set.uIcc_of_le hY] at hy
    simp only [L.cdf_inv hy.1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    by_cases hp : L.prob j = 0
    · simp [hp]
    · rw [L.integral_slope_after (L.ramp_nonneg _) (hS j hp)]
  · intro j _
    refine intervalIntegrable_of_bounded (C := |L.prob j| * (1 / L.cdf L.low)) ?_ (fun y => ?_) 0 Y
    · exact measurable_const.mul ((L.slope_measurable.comp (measurable_add_const 1)).mul
        (Measurable.ite measurableSet_Ici measurable_const measurable_const))
    · rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      split_ifs
      · rw [mul_one]; exact L.abs_slope_le _
      · rw [mul_zero, abs_zero]; exact (one_div_pos.mpr L.cdf_low_pos).le

theorem sum_prob_mul_sub (a : ℝ) (b : ι → ℝ) :
    ∑ j, L.prob j * (a - b j) = a - ∑ j, L.prob j * b j := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, L.prob_sum, one_mul]

theorem div_slope (x y : ℝ) : x / L.slope y = x * L.cdf (L.inv y) := by
  rw [slope, div_div_eq_mul_div, div_one]

/-- Beyond every left endpoint, `Y = H(X(Y)) = X(Y) - B`. -/
theorem inv_eq_of_ge {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    L.inv Y = Y + L.mean := by
  have h := L.ramp_of_ge hX
  rw [L.ramp_inv hY] at h
  linarith

theorem inv_add_one {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    L.inv (Y + 1) = L.inv Y + 1 := by
  have h : L.ramp (L.inv Y + 1) = Y + 1 := by
    rw [L.ramp_of_ge fun j => (hX j).trans (by linarith), L.inv_eq_of_ge hY hX]
    ring
  rw [← h, L.inv_ramp (by linarith [L.low_le_inv Y])]

theorem measurable_adaptation :
    Measurable fun y => 1 - L.slope (y + 1) * L.cdf (L.inv y) :=
  measurable_const.sub ((L.slope_measurable.comp (measurable_add_const 1)).mul
    (L.cdf_mono.comp L.inv_mono).measurable)

theorem abs_adaptation_le (y : ℝ) :
    |1 - L.slope (y + 1) * L.cdf (L.inv y)| ≤ 1 + 1 / L.cdf L.low := by
  have h1 := L.one_le_slope (y + 1)
  have h2 := L.slope_le (y + 1)
  have h3 := L.cdf_nonneg (L.inv y)
  have h4 := L.cdf_le_one (L.inv y)
  rw [abs_le]
  constructor <;> nlinarith

/-- Identity (11): `∫_0^Y (1 - g(y + 1) / g(y)) dy = C - 1` for the extended intervals
`[ℓ_j, X(H(ℓ_j) + 1)]`, once `Y` lies beyond every `H(ℓ_j)` and `X(Y)` beyond every `ℓ_j`. -/
theorem integral_adaptation {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    ∫ y in (0 : ℝ)..Y, (1 - L.slope (y + 1) * L.cdf (L.inv y)) =
      ∑ j, L.prob j * (L.inv (L.ramp (L.left j) + 1) - L.left j) - 1 := by
  have hint : IntervalIntegrable (fun y => L.slope (y + 1) * L.cdf (L.inv y)) volume 0 Y := by
    refine intervalIntegrable_of_bounded (f := fun y => L.slope (y + 1) * L.cdf (L.inv y))
      (C := 1 / L.cdf L.low) ((L.slope_measurable.comp (measurable_add_const 1)).mul
        (L.cdf_mono.comp L.inv_mono).measurable) (fun y => ?_) 0 Y
    rw [abs_mul, abs_of_nonneg (L.cdf_nonneg _)]
    calc |L.slope (y + 1)| * L.cdf (L.inv y) ≤ (1 / L.cdf L.low) * 1 :=
          mul_le_mul (L.abs_slope_le _) (L.cdf_le_one _) (L.cdf_nonneg _)
            (one_div_pos.mpr L.cdf_low_pos).le
      _ = 1 / L.cdf L.low := mul_one _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hint, intervalIntegral.integral_const,
    L.integral_slope_mul_cdf hY hS, L.sum_prob_mul_sub, L.inv_add_one hY hX,
    L.inv_eq_of_ge hY hX, smul_eq_mul, mul_one, sub_zero]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [mean]
  ring

/-- Identity (10): `∫_0^Y (g - 1) = B - low` once `X(Y)` lies beyond every left endpoint. -/
theorem integral_slope_sub_one {Y : ℝ} (hY : 0 ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    ∫ y in (0 : ℝ)..Y, (L.slope y - 1) = L.mean - L.low := by
  rw [intervalIntegral.integral_sub
      (intervalIntegrable_of_bounded L.slope_measurable L.abs_slope_le 0 Y) intervalIntegrable_const,
    L.integral_slope le_rfl hY, intervalIntegral.integral_const, L.inv_zero,
    L.inv_eq_of_ge hY hX, smul_eq_mul, mul_one, sub_zero]
  ring

theorem intervalIntegrable_sum_shift {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun s => ∑ j ∈ Finset.range N, φ (s + j)) volume a b := by
  refine intervalIntegrable_of_bounded (C := N * C)
    (Finset.measurable_sum _ fun j _ => hφ.comp (measurable_add_const _)) (fun s => ?_) a b
  calc |∑ j ∈ Finset.range N, φ (s + j)| ≤ ∑ j ∈ Finset.range N, |φ (s + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range N, C := Finset.sum_le_sum fun j _ => hC _
    _ = N * C := by simp

/-- **Inequality (7) after normalization.** If `H(r_i) - H(ℓ_i) = ∫_{ℓ_i}^{r_i} W ≤ 1` for every
interval of positive probability, then `α (B + C) ≤ B + 1`. The intervals are extended to
`[ℓ_i, X(H(ℓ_i) + 1)]` (9), which can only increase `C`; for these, averaging the chain bound
over the chains `g(s), g(s + 1), …, g(s + N) = 1`, `s ∈ [0, 1]`, and using (10) and (11) gives
`α (C - 1) ≤ (1 - α) (1 + B - low)`. -/
theorem core {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j)
    (hM : ∀ j, L.prob j ≠ 0 → L.ramp (r j) - L.ramp (L.left j) ≤ 1) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + 1 := by
  -- `U` bounds every left endpoint, and beyond `N ≥ H(U)` we have `X ≥ U` and `g = 1`.
  have hUl : ∀ j, L.left j ≤ |L.low| + ∑ i, |L.left i| := fun j => by
    have := Finset.single_le_sum (f := fun i => |L.left i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [le_abs_self (L.left j), abs_nonneg L.low]
  have hUlow : L.low ≤ |L.low| + ∑ i, |L.left i| := by
    have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (L.left i)
    linarith [le_abs_self L.low]
  set U := |L.low| + ∑ i, |L.left i|
  set N : ℕ := ⌈L.ramp U⌉₊
  have hN : L.ramp U ≤ N := Nat.le_ceil _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbeyond : ∀ y : ℝ, (N : ℝ) ≤ y → ∀ j, L.left j ≤ L.inv y := fun y hy j =>
    calc L.left j ≤ U := hUl j
      _ = L.inv (L.ramp U) := (L.inv_ramp hUlow).symm
      _ ≤ L.inv y := L.inv_mono (hN.trans hy)
  have hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ N := fun j _ =>
    (L.ramp_mono (hUl j)).trans hN
  -- The extension (9): `r_j ≤ X(H(ℓ_j) + 1)`.
  have hext : ∑ j, L.prob j * (r j - L.left j) ≤
      ∑ j, L.prob j * (L.inv (L.ramp (L.left j) + 1) - L.left j) := by
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hp : L.prob j = 0
    · simp [hp]
    · refine mul_le_mul_of_nonneg_left (sub_le_sub_right ?_ _) (L.prob_nonneg j)
      calc r j = L.inv (L.ramp (r j)) := (L.inv_ramp ((L.low_le j hp).trans (hr j hp))).symm
        _ ≤ L.inv (L.ramp (L.left j) + 1) := L.inv_mono (by linarith [hM j hp])
  -- The chain bound for `g(s), g(s + 1), …, g(s + N) = 1` at every `s ∈ [0, 1]`.
  have hpoint : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      α * ∑ j ∈ Finset.range N, (1 - L.slope (s + j + 1) * L.cdf (L.inv (s + j))) ≤
        (1 - α) * (1 + ∑ j ∈ Finset.range N, (L.slope (s + j) - 1)) := by
    intro s hs
    have h := chain_bound hα0 hchain (N := N) (d := fun j => L.slope (s + j))
      (fun j _ => L.slope_antitone (by push_cast; linarith))
      (by simp only [slope]; rw [L.cdf_eq_one (hbeyond _ (by linarith [hs.1])), div_one])
    have hsum : ∑ j ∈ Finset.range N, (1 - L.slope (s + j + 1) * L.cdf (L.inv (s + j))) =
        ∑ j ∈ Finset.range N, (1 - L.slope (s + ↑(j + 1)) / L.slope (s + j)) :=
      Finset.sum_congr rfl fun j _ => by rw [L.div_slope, Nat.cast_succ, add_assoc]
    rw [hsum]
    exact h
  have hm₁ := L.measurable_adaptation
  have hm₂ : Measurable fun y => L.slope y - 1 := L.slope_measurable.sub measurable_const
  have hb₂ : ∀ y, |L.slope y - 1| ≤ 1 / L.cdf L.low + 1 := fun y => by
    have := L.abs_slope_le y
    calc |L.slope y - 1| ≤ |L.slope y| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 1 / L.cdf L.low + 1 := by rw [abs_one]; linarith
  have hint := intervalIntegral.integral_mono_on zero_le_one
    ((intervalIntegrable_sum_shift hm₁ L.abs_adaptation_le N 0 1).const_mul α)
    ((IntervalIntegrable.add intervalIntegrable_const
      (intervalIntegrable_sum_shift hm₂ hb₂ N 0 1)).const_mul (1 - α)) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add intervalIntegrable_const
      (intervalIntegrable_sum_shift hm₂ hb₂ N 0 1),
    integral_sum_shift hm₁ L.abs_adaptation_le N, integral_sum_shift hm₂ hb₂ N,
    L.integral_adaptation hN0 hS (hbeyond N le_rfl),
    L.integral_slope_sub_one hN0 (hbeyond N le_rfl), intervalIntegral.integral_const,
    smul_eq_mul, sub_zero, mul_one] at hint
  nlinarith [mul_le_mul_of_nonneg_left hext hα0, mul_nonneg (sub_nonneg.mpr hα1) hlow]

/-- The law with every endpoint divided by `M > 0`. -/
def scale (M : ℝ) (hM : 0 < M) : LeftLaw ι where
  prob := L.prob
  left j := L.left j / M
  low := L.low / M
  prob_nonneg := L.prob_nonneg
  prob_sum := L.prob_sum
  low_le j hj := div_le_div_of_nonneg_right (L.low_le j hj) hM.le
  atom := by
    obtain ⟨j, hj, hjl⟩ := L.atom
    exact ⟨j, hj, div_le_div_of_nonneg_right hjl hM.le⟩

/-- **Inequality (7).** If every interval of positive probability has
`Σ_j p_j |[ℓ_i, r_i] ∩ [ℓ_j, ∞)| ≤ M`, then `α (B + C) ≤ B + M`. For `M > 0` this is `core`
after dividing every endpoint by `M`; for `M ≤ 0` every such interval is a point. -/
theorem core_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j) {M : ℝ}
    (hM : ∀ i, L.prob i ≠ 0 → ∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j)) ≤ M) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + M := by
  have hmean : 0 ≤ L.mean := Finset.sum_nonneg fun j _ => by
    by_cases hp : L.prob j = 0
    · simp [hp]
    · exact mul_nonneg (L.prob_nonneg j) (hlow.trans (L.low_le j hp))
  rcases lt_or_ge 0 M with hM0 | hM0
  · -- Divide every endpoint by `M`.
    have hscaled := (L.scale M hM0).core hα0 hα1 hchain (div_nonneg hlow hM0.le)
      (fun j => r j / M) (fun j hj => div_le_div_of_nonneg_right (hr j hj) hM0.le)
      (fun i hi => by
        have hle : L.left i / M ≤ r i / M := div_le_div_of_nonneg_right (hr i hi) hM0.le
        show (L.scale M hM0).ramp (r i / M) - (L.scale M hM0).ramp (L.left i / M) ≤ 1
        rw [(L.scale M hM0).ramp_sub hle]
        calc _ = (∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j))) / M := by
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [scale]
              rw [max_div_div_right hM0.le, ← sub_div, ← zero_div M,
                max_div_div_right hM0.le, zero_div, mul_div_assoc]
          _ ≤ M / M := div_le_div_of_nonneg_right (hM i hi) hM0.le
          _ = 1 := div_self hM0.ne')
    have hmean' : (L.scale M hM0).mean = L.mean / M := by
      simp only [mean, scale, Finset.sum_div, mul_div_assoc]
    have hC' : ∑ j, (L.scale M hM0).prob j * (r j / M - (L.scale M hM0).left j) =
        (∑ j, L.prob j * (r j - L.left j)) / M := by
      simp only [scale, Finset.sum_div, ← sub_div, mul_div_assoc]
    rw [hmean', hC'] at hscaled
    have h := mul_le_mul_of_nonneg_left hscaled hM0.le
    have e1 : M * (α * (L.mean / M + (∑ j, L.prob j * (r j - L.left j)) / M)) =
        α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) := by
      field_simp
    have e2 : M * (L.mean / M + 1) = L.mean + M := by field_simp
    rw [e1, e2] at h
    exact h
  · -- `M ≤ 0`: every interval of positive probability is a point, so `C = 0`.
    have hpoint : ∀ i, L.prob i ≠ 0 → L.prob i * (r i - L.left i) ≤ M := fun i hi =>
      calc L.prob i * (r i - L.left i)
          = L.prob i * max 0 (r i - max (L.left i) (L.left i)) := by
            rw [max_self, max_eq_right (sub_nonneg.mpr (hr i hi))]
        _ ≤ ∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j)) :=
            Finset.single_le_sum (f := fun j => L.prob j * max 0 (r i - max (L.left i) (L.left j)))
              (fun j _ => mul_nonneg (L.prob_nonneg j) (le_max_left _ _)) (Finset.mem_univ i)
        _ ≤ M := hM i hi
    have hC : ∑ j, L.prob j * (r j - L.left j) = 0 := Finset.sum_eq_zero fun j _ => by
      by_cases hp : L.prob j = 0
      · simp [hp]
      · exact le_antisymm ((hpoint j hp).trans hM0)
          (mul_nonneg (L.prob_nonneg j) (sub_nonneg.mpr (hr j hp)))
    obtain ⟨i, hi, -⟩ := L.atom
    have hM0' : 0 ≤ M := (Finset.sum_nonneg fun j _ =>
      mul_nonneg (L.prob_nonneg j) (le_max_left _ _)).trans (hM i hi)
    rw [hC, add_zero]
    nlinarith

end LeftLaw

end ConsistentSubmodular.Shadow
