module

public import ConsistentSubmodular.Deterministic.Basic.SamplingOperators

@[expose] public section

/-!
# Concentration for independent inclusion (Lemma B.7)

The two concentration bounds of Lemma B.7 (Appendix B.2.3), for a random set
that contains each coordinate `i` of a finite set `U` independently with
probability `p i`.

* `sampleExpectation_lower_tail_le` is the lower tail (37) of a monotone
  submodular function whose marginals are at most `c`: falling `a` below the
  mean has probability at most `exp (-a² / (2 c M))` when the mean exceeds the
  value of the empty set by at most `M`; with `M = μ` this is (37).
* `sampleExpectation_card_chernoff` is the multiplicative Chernoff bound (38)
  for the cardinality, and `sampleExpectation_card_upper_tail` is the additive
  form with exponent `-b² / (4 κ)` that the rounding of Theorem 5 uses.

The paper cites both bounds: (37) is Vondrák [2010, Corollary 3.2], and (38) is
the standard Chernoff bound. Here (37) follows from the exponential moment
bound `E[exp (-λ G)] ≤ exp (-λ G(∅) + (E G - G(∅)) (exp (-λ) - 1))`, which says
that `G` is at least as concentrated below its mean as a sum of independent
indicators with the same mean; it is proved by induction on the coordinates,
using only monotonicity, submodularity, and the marginal bound.
-/
noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

/-- `exp (-x) ≤ 1 - x + x² / 2` for `x ≥ 0`. -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hcubic : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 ≤ Real.exp x := by
    have h := Real.sum_le_exp_of_nonneg hx 4
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
      Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one,
      zero_add, div_one] at h
    linarith
  have hprod : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos x
  have hA : 0 < 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  have hkey : 1 ≤ (1 - x + x ^ 2 / 2) * Real.exp x := by
    have hm := mul_le_mul_of_nonneg_left hcubic hA.le
    nlinarith [pow_nonneg hx 3, pow_nonneg hx 4, pow_nonneg hx 5]
  by_contra h
  have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge h) hpos
  linarith

/-- The scalar inequality behind one coordinate of the exponential-moment
induction: `δ` is the mean marginal and `d` the marginal at the empty set. -/
theorem exp_moment_step {lam p δ d : ℝ} (hp0 : 0 ≤ p)
    (hδ0 : 0 ≤ δ) (hδd : δ ≤ d) (hd1 : d ≤ 1) :
    (1 - p) + p * Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      Real.exp (p * δ * (Real.exp (-lam) - 1)) := by
  have hd0 : 0 ≤ d := hδ0.trans hδd
  have hlow : 1 - lam ≤ Real.exp (-lam) := Real.one_sub_le_exp_neg lam
  have hy : Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      1 + δ * (Real.exp (-lam) - 1) := by
    rcases eq_or_lt_of_le hd0 with hd | hd
    · have hδ : δ = 0 := le_antisymm (by rw [hd]; exact hδd) hδ0
      rw [hδ, ← hd]
      simp
    · set t := Real.exp (-lam) - 1 with htdef
      set θ := δ / d with hθ
      have hθ0 : 0 ≤ θ := div_nonneg hδ0 hd0
      have hθ1 : θ ≤ 1 := (div_le_one hd).mpr hδd
      have hδθ : δ = θ * d := by rw [hθ]; field_simp
      have hcomb : -lam * d + (δ - d) * t = (1 - θ) * (-lam * d - d * t) + θ * (-lam * d) := by
        rw [hδθ]; ring
      have hconv := convexOn_exp.2 (Set.mem_univ (-lam * d - d * t)) (Set.mem_univ (-lam * d))
        (sub_nonneg.mpr hθ1) hθ0 (by ring)
      simp only [smul_eq_mul] at hconv
      have h1 : Real.exp (-lam * d - d * t) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        nlinarith [mul_nonneg hd0 (show 0 ≤ lam + t by linarith)]
      have h2 : Real.exp (-lam * d) ≤ 1 + d * t := by
        have hc := convexOn_exp.2 (Set.mem_univ (-lam)) (Set.mem_univ (0 : ℝ)) hd0
          (sub_nonneg.mpr hd1) (by ring)
        simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hc
        have he : -lam * d = d * -lam := by ring
        rw [he]
        linarith
      rw [hcomb]
      calc Real.exp ((1 - θ) * (-lam * d - d * t) + θ * (-lam * d))
          ≤ (1 - θ) * Real.exp (-lam * d - d * t) + θ * Real.exp (-lam * d) := hconv
        _ ≤ (1 - θ) * 1 + θ * (1 + d * t) := by
          nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hθ1),
            mul_le_mul_of_nonneg_left h2 hθ0]
        _ = 1 + δ * t := by rw [hδθ]; ring
  have hmain : (1 - p) + p * Real.exp (-lam * d + (δ - d) * (Real.exp (-lam) - 1)) ≤
      1 + p * δ * (Real.exp (-lam) - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hy hp0]
  exact hmain.trans (by linarith [Real.add_one_le_exp (p * δ * (Real.exp (-lam) - 1))])

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_le_const (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ} {c : ℝ}
    (hv : ∀ S ⊆ U, v S ≤ c) : sampleExpectation U p v ≤ c := by
  have h := sampleExpectation_mono U p hp (v := v) (w := fun _ => c) hv
  rwa [sampleExpectation_const] at h

theorem const_le_sampleExpectation (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {v : Finset ι → ℝ} {c : ℝ}
    (hv : ∀ S ⊆ U, c ≤ v S) : c ≤ sampleExpectation U p v := by
  have h := sampleExpectation_mono U p hp (v := fun _ => c) (w := v) hv
  rwa [sampleExpectation_const] at h

/-- The exponential moment of a monotone submodular function with marginals at
most one, as for a sum of independent indicators with the same mean. -/
theorem sampleExpectation_exp_neg_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    (hcap : ∀ A e, G (insert e A) - G A ≤ 1) (lam : ℝ) :
    sampleExpectation U p (fun S => Real.exp (-lam * G S)) ≤
      Real.exp (-lam * G ∅ + (sampleExpectation U p G - G ∅) * (Real.exp (-lam) - 1)) := by
  induction U using Finset.induction_on generalizing G with
  | empty => simp
  | @insert u U hu ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨hpu0, hpu1⟩ := hp u (Finset.mem_insert_self u U)
    let G1 : Finset ι → ℝ := fun S => G (insert u S)
    have h1mono : ∀ A B, A ⊆ B → G1 A ≤ G1 B :=
      fun A B h => hmono _ _ (Finset.insert_subset_insert u h)
    have h1sub : ∀ A B, G1 (A ∪ B) + G1 (A ∩ B) ≤ G1 A + G1 B := by
      intro A B
      have h := hsub (insert u A) (insert u B)
      have hu1 : insert u (A ∪ B) = insert u A ∪ insert u B := by
        ext e; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      have hu2 : insert u (A ∩ B) = insert u A ∩ insert u B := by
        ext e; simp only [Finset.mem_insert, Finset.mem_inter]; tauto
      simp only [G1, hu1, hu2]
      exact h
    have h1cap : ∀ A e, G1 (insert e A) - G1 A ≤ 1 := by
      intro A e
      simp only [G1]
      rw [Finset.insert_comm]
      exact hcap _ e
    have h0 := ih hpU G hmono hsub hcap
    have h1 := ih hpU G1 h1mono h1sub h1cap
    have hG1 : G1 ∅ = G {u} := by simp [G1]
    rw [hG1] at h1
    -- The mean marginal of `u` lies between zero and its marginal at the empty set.
    have hδ : sampleExpectation U p G1 - sampleExpectation U p G =
        sampleExpectation U p (fun S => G (insert u S) - G S) := by
      rw [sampleExpectation_sub]
    have hδ0 : 0 ≤ sampleExpectation U p G1 - sampleExpectation U p G := by
      rw [hδ]
      exact sampleExpectation_nonnegative U p hpU (fun S _ =>
        sub_nonneg.mpr (hmono _ _ (Finset.subset_insert u S)))
    have hδd : sampleExpectation U p G1 - sampleExpectation U p G ≤ G {u} - G ∅ := by
      rw [hδ]
      apply sampleExpectation_le_const U p hpU
      intro S hS
      have huS : u ∉ S := fun h => hu (hS h)
      have h := hsub S {u}
      have hi : S ∩ {u} = ∅ := by
        ext e; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false, not_and]
        rintro he rfl; exact huS he
      have hun : S ∪ {u} = insert u S := by
        ext e; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto
      rw [hi, hun] at h
      linarith
    have hd1 : G {u} - G ∅ ≤ 1 := by simpa using hcap ∅ u
    have hstep := exp_moment_step (lam := lam) hpu0 hδ0 hδd hd1
    rw [sampleExpectation_insert U hu, sampleExpectation_insert U hu]
    change (1 - p u) * sampleExpectation U p (fun S => Real.exp (-lam * G S)) +
        p u * sampleExpectation U p (fun S => Real.exp (-lam * G1 S)) ≤ _
    obtain ⟨a, ha⟩ : ∃ a, a = -lam * G ∅ +
        (sampleExpectation U p G - G ∅) * (Real.exp (-lam) - 1) := ⟨_, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x, x = -lam * (G {u} - G ∅) +
        ((sampleExpectation U p G1 - sampleExpectation U p G) - (G {u} - G ∅)) *
          (Real.exp (-lam) - 1) := ⟨_, rfl⟩
    have h0' : sampleExpectation U p (fun S => Real.exp (-lam * G S)) ≤ Real.exp a := by
      rw [ha]; exact h0
    have h1' : sampleExpectation U p (fun S => Real.exp (-lam * G1 S)) ≤
        Real.exp a * Real.exp x := by
      rw [← Real.exp_add]
      refine h1.trans (le_of_eq ?_)
      congr 1
      rw [ha, hx]
      ring
    rw [← hx] at hstep
    have hpos := Real.exp_pos a
    have hgoal : -lam * G ∅ + ((1 - p u) * sampleExpectation U p G +
        p u * sampleExpectation U p (fun S => G (insert u S)) - G ∅) * (Real.exp (-lam) - 1) =
        a + p u * (sampleExpectation U p G1 - sampleExpectation U p G) *
          (Real.exp (-lam) - 1) := by
      rw [ha]; ring
    rw [hgoal, Real.exp_add]
    calc (1 - p u) * sampleExpectation U p (fun S => Real.exp (-lam * G S)) +
          p u * sampleExpectation U p (fun S => Real.exp (-lam * G1 S))
        ≤ (1 - p u) * Real.exp a + p u * (Real.exp a * Real.exp x) :=
          add_le_add (mul_le_mul_of_nonneg_left h0' (by linarith))
            (mul_le_mul_of_nonneg_left h1' hpu0)
      _ = Real.exp a * ((1 - p u) + p u * Real.exp x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstep hpos.le

/-- The lower tail (37): a monotone submodular function with marginals at most
`c`, whose mean exceeds its empty value by at most `M`, falls to `a` below its
mean or lower with probability at most `exp (-a² / (2 c M))`. -/
theorem sampleExpectation_lower_tail_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    {c M a : ℝ} (hc : 0 < c) (hcap : ∀ A e, G (insert e A) - G A ≤ c) (hM : 0 < M)
    (hmean : sampleExpectation U p G - G ∅ ≤ M) (ha : 0 ≤ a) :
    sampleExpectation U p (fun S => if G S ≤ sampleExpectation U p G - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * M)) := by
  set μ := sampleExpectation U p G with hμ
  let G' : Finset ι → ℝ := fun S => G S / c
  have h'mono : ∀ A B, A ⊆ B → G' A ≤ G' B :=
    fun A B h => div_le_div_of_nonneg_right (hmono A B h) hc.le
  have h'sub : ∀ A B, G' (A ∪ B) + G' (A ∩ B) ≤ G' A + G' B := by
    intro A B
    simp only [G', ← add_div]
    exact div_le_div_of_nonneg_right (hsub A B) hc.le
  have h'cap : ∀ A e, G' (insert e A) - G' A ≤ 1 := by
    intro A e
    simp only [G', ← sub_div]
    exact (div_le_one hc).mpr (hcap A e)
  set lam := a / M with hlamdef
  have hlam : 0 ≤ lam := div_nonneg ha hM.le
  have hmgf := sampleExpectation_exp_neg_le U p hp G' h'mono h'sub h'cap lam
  have hmean' : sampleExpectation U p G' = μ / c := by
    have h := sampleExpectation_mul U p (1 / c) G
    simp only [G', div_eq_mul_inv, one_mul] at h ⊢
    rw [mul_comm] at h
    rw [show (fun S => G S * c⁻¹) = (fun S => c⁻¹ * G S) from funext (fun S => mul_comm _ _), h,
      mul_comm]
  have hpoint : ∀ S ⊆ U, (if G S ≤ μ - a then (1 : ℝ) else 0) ≤
      Real.exp (lam * (μ - a) / c) * Real.exp (-lam * G' S) := by
    intro S _
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      have hdiff : 0 ≤ (μ - a - G S) / c := div_nonneg (by linarith) hc.le
      have he : lam * (μ - a) / c + -lam * G' S = lam * ((μ - a - G S) / c) := by
        simp only [G']; ring
      rw [he]
      exact mul_nonneg hlam hdiff
    · exact (Real.exp_pos _).le
  have hP := sampleExpectation_mono U p hp hpoint
  rw [sampleExpectation_mul] at hP
  have hbound := hP.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
  rw [← Real.exp_add, hmean'] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  -- The exponent is at most `-a² / (2 c M)`.
  have hm0 : 0 ≤ (μ - G ∅) / c := by
    have h := const_le_sampleExpectation U p hp (v := G) (c := G ∅)
      (fun S _ => hmono _ _ (Finset.empty_subset S))
    exact div_nonneg (by rw [hμ]; linarith) hc.le
  have hmM : (μ - G ∅) / c ≤ M / c := div_le_div_of_nonneg_right hmean hc.le
  have hq0 : 0 ≤ lam + Real.exp (-lam) - 1 := by linarith [Real.one_sub_le_exp_neg lam]
  have hq1 : lam + Real.exp (-lam) - 1 ≤ lam ^ 2 / 2 := by
    linarith [exp_neg_le_quadratic hlam]
  have hprod : (μ - G ∅) / c * (lam + Real.exp (-lam) - 1) ≤ M / c * (lam ^ 2 / 2) :=
    mul_le_mul hmM hq1 hq0 (div_nonneg hM.le hc.le)
  have hexp : lam * (μ - a) / c + (-lam * G' ∅ + (μ / c - G' ∅) * (Real.exp (-lam) - 1)) =
      -(lam * a / c) + (μ - G ∅) / c * (lam + Real.exp (-lam) - 1) := by
    simp only [G']; ring
  rw [hexp]
  have hfinal : -(lam * a / c) + M / c * (lam ^ 2 / 2) = -(a ^ 2) / (2 * c * M) := by
    rw [hlamdef]
    field_simp
    ring
  linarith

/-- The lower tail (37) for the strict event `G(S) < μ - a`. -/
theorem sampleExpectation_lower_tail (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    {c M a : ℝ} (hc : 0 < c) (hcap : ∀ A e, G (insert e A) - G A ≤ c) (hM : 0 < M)
    (hmean : sampleExpectation U p G - G ∅ ≤ M) (ha : 0 ≤ a) :
    sampleExpectation U p (fun S => if G S < sampleExpectation U p G - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * M)) := by
  refine (sampleExpectation_mono U p hp fun S _ => ?_).trans
    (sampleExpectation_lower_tail_le U p hp G hmono hsub hc hcap hM hmean ha)
  split_ifs with h h'
  · exact le_rfl
  · exact absurd h.le h'
  · exact zero_le_one
  · exact le_rfl

/-- The exponential moment of the cardinality of an independent sample. -/
theorem sampleExpectation_exp_card_le (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {s : ℝ} (hs : 0 ≤ s) :
    sampleExpectation U p (fun S => Real.exp (s * S.card)) ≤
      Real.exp ((Real.exp s - 1) * ∑ i ∈ U, p i) := by
  induction U using Finset.induction_on with
  | empty => simp
  | @insert u U hu ih =>
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (Finset.mem_insert_of_mem hi)
    obtain ⟨hpu0, hpu1⟩ := hp u (Finset.mem_insert_self u U)
    rw [sampleExpectation_insert U hu]
    have hcongr : sampleExpectation U p (fun S => Real.exp (s * ((insert u S).card : ℝ))) =
        Real.exp s * sampleExpectation U p (fun S => Real.exp (s * S.card)) := by
      rw [← sampleExpectation_mul]
      apply sampleExpectation_congr
      intro S hS
      have huS : u ∉ S := fun h => hu (hS h)
      rw [Finset.card_insert_of_notMem huS]
      push_cast
      rw [mul_add, mul_one, Real.exp_add]
      ring
    rw [hcongr, Finset.sum_insert hu]
    have hE0 : 0 ≤ sampleExpectation U p (fun S => Real.exp (s * S.card)) :=
      sampleExpectation_nonnegative U p hpU (fun S _ => (Real.exp_pos _).le)
    have hes : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
    calc (1 - p u) * sampleExpectation U p (fun S => Real.exp (s * S.card)) +
          p u * (Real.exp s * sampleExpectation U p (fun S => Real.exp (s * S.card)))
        = (1 + p u * (Real.exp s - 1)) *
            sampleExpectation U p (fun S => Real.exp (s * S.card)) := by ring
      _ ≤ Real.exp (p u * (Real.exp s - 1)) *
            Real.exp ((Real.exp s - 1) * ∑ i ∈ U, p i) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (p u * (Real.exp s - 1))]) (ih hpU) hE0
            (Real.exp_pos _).le
      _ = Real.exp ((Real.exp s - 1) * (p u + ∑ i ∈ U, p i)) := by
          rw [← Real.exp_add]; ring_nf

/-- The additive cardinality tail: an independent sample of expected size at
most `κ` exceeds `κ + b` with probability at most `exp (-b² / (4 κ))`. -/
theorem sampleExpectation_card_upper_tail (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ b : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hb : 0 < b) (hb2 : b ≤ 2 * κ) :
    sampleExpectation U p (fun S => if κ + b < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(b ^ 2) / (4 * κ)) := by
  have hκ : 0 < κ := by linarith
  set s := b / (2 * κ) with hsdef
  have hs0 : 0 ≤ s := div_nonneg hb.le (by linarith)
  have hs1 : s ≤ 1 := (div_le_one (by linarith)).mpr hb2
  have hpoint : ∀ S ⊆ U, (if κ + b < (S.card : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-s * (κ + b)) * Real.exp (s * S.card) := by
    intro S _
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      nlinarith
    · exact (Real.exp_pos _).le
  have hP := sampleExpectation_mono U p hp hpoint
  rw [sampleExpectation_mul] at hP
  have hmgf := sampleExpectation_exp_card_le U p hp hs0
  have hbound := hP.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
  rw [← Real.exp_add] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hes : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hquad : Real.exp s - 1 ≤ s + s ^ 2 := by
    have h := Real.abs_exp_sub_one_sub_id_le (x := s) (by rw [abs_of_nonneg hs0]; exact hs1)
    linarith [le_abs_self (Real.exp s - 1 - s)]
  have hm := mul_le_mul_of_nonneg_left hmass hes
  have hκs : (Real.exp s - 1) * κ ≤ (s + s ^ 2) * κ := mul_le_mul_of_nonneg_right hquad hκ.le
  have hfinal : -s * (κ + b) + (s + s ^ 2) * κ = -(b ^ 2) / (4 * κ) := by
    rw [hsdef]
    field_simp
    ring
  linarith


/-- `exp s ≤ 1 + s + s²/2 + 2 s³/9` for `0 ≤ s ≤ 1`. -/
theorem exp_le_cubic {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp s ≤ 1 + s + s ^ 2 / 2 + 2 / 9 * s ^ 3 := by
  have h := Real.exp_bound' hs0 hs1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_one,
    Nat.cast_ofNat, Nat.succ_eq_add_one, Nat.reduceAdd, Nat.reduceMul, pow_zero, pow_one,
    zero_add, div_one] at h
  linarith

/-- The multiplicative Chernoff bound (38): an independent sample of expected
size at most `κ` exceeds `(1 + η) κ` with probability at most
`exp (-η² κ / 3)` for `0 < η ≤ 1`. The exponential moment of `|S|` at
`s = η - η²/3` gives the exponent `κ (e^s - 1 - s (1 + η)) ≤ -η² κ / 3`. -/
theorem sampleExpectation_card_chernoff (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) {κ η : ℝ} (hmass : ∑ i ∈ U, p i ≤ κ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    sampleExpectation U p (fun S => if (1 + η) * κ < (S.card : ℝ) then 1 else 0) ≤
      Real.exp (-(η ^ 2) * κ / 3) := by
  have hκ : 0 ≤ κ := (Finset.sum_nonneg fun i hi => (hp i hi).1).trans hmass
  set s := η - η ^ 2 / 3 with hsdef
  have hs0 : 0 ≤ s := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith
  have hpoint : ∀ S ⊆ U, (if (1 + η) * κ < (S.card : ℝ) then (1 : ℝ) else 0) ≤
      Real.exp (-s * ((1 + η) * κ)) * Real.exp (s * S.card) := by
    intro S _
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp_iff.mpr
      nlinarith
    · exact (Real.exp_pos _).le
  have hP := sampleExpectation_mono U p hp hpoint
  rw [sampleExpectation_mul] at hP
  have hmgf := sampleExpectation_exp_card_le U p hp hs0
  have hbound := hP.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le)
  rw [← Real.exp_add] at hbound
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hes : 0 ≤ Real.exp s - 1 := by linarith [Real.add_one_le_exp s]
  have hm := mul_le_mul_of_nonneg_left hmass hes
  have hcubic := exp_le_cubic hs0 hs1
  -- `e^s - 1 - s (1 + η) ≤ -η²/3` at `s = η - η²/3`, for `0 < η ≤ 1`.
  have hkey : Real.exp s - 1 - s * (1 + η) ≤ -(η ^ 2) / 3 := by
    have hpoly : s + s ^ 2 / 2 + 2 / 9 * s ^ 3 - s * (1 + η) ≤ -(η ^ 2) / 3 := by
      rw [hsdef]
      nlinarith [sq_nonneg (η - 2 / 3), pow_le_one₀ hη.le hη1 (n := 3), pow_nonneg hη.le 4,
        mul_nonneg (sq_nonneg η) (sq_nonneg (η - 2 / 3)), mul_nonneg (pow_nonneg hη.le 3)
          (sub_nonneg.mpr hη1), sq_nonneg η]
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hkey hκ]

namespace Tails

/-- **Lemma B.7** (concentration), for a random subset of `{0, ..., d - 1}`. -/
theorem concentration : ConcentrationGoal := by
  refine ⟨fun d q G c a hq hG hmono hsub hc hcap => ?_, fun d q κ η hq hmass hη hη1 => ?_⟩
  · dsimp only
    intro ha haμ
    have hEq : independentExpectation Finset.univ q G = sampleExpectation Finset.univ q G := rfl
    rw [hEq] at haμ ⊢
    have hp : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ q i ∧ q i ≤ 1 := fun i _ => hq i
    exact sampleExpectation_lower_tail_le Finset.univ q hp G hmono hsub hc hcap (ha.trans haμ)
      (by linarith [hG ∅]) ha.le
  · exact sampleExpectation_card_chernoff Finset.univ q (fun i _ => hq i) hmass hη hη1

end Tails

end ConsistentSubmodular
