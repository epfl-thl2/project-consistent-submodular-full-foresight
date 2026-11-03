module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# Checkpoint instances

At a checkpoint `τ`, Algorithm 1 (Appendix A.3) calls the addition-robust
routine with `V_now = X_τ`, the elements arrived so far, and with
`V_future = (x_{τ+1}, ..., x_n)`, the rest of the stream. This file builds that
instance of the clairvoyant addition-robust problem and proves the two facts
that the proof of Lemma 1 uses: the benchmark of every future prefix dominates
every set of at most `κ` arrived elements, and the proportional subset bound
`f(OPT_t^(κ)) ≥ (κ/k) f(OPT_t)`. The paper obtains the subset by sampling `κ`
elements of `OPT_t` uniformly; here it comes from repeated deletion, as in the
proof of the thinning inequality (43) of Appendix B.2.4.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-! ### Submodular facts -/

/-- Diminishing returns: adding `e` to a larger set gains less. -/
theorem marginal_le (f : Objective n) {X Y : Finset (Fin n)} (hYX : Y ⊆ X) (e : Fin n) :
    f.value (insert e X) - f.value X ≤ f.value (insert e Y) - f.value Y := by
  by_cases heX : e ∈ X
  · rw [Finset.insert_eq_of_mem heX, sub_self]
    exact sub_nonneg.mpr (f.monotone _ _ (Finset.subset_insert e Y))
  · have hsub := f.submodular X (insert e Y)
    have hu : X ∪ insert e Y = insert e X := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (hx | rfl | hx)
        · exact Or.inr hx
        · exact Or.inl rfl
        · exact Or.inr (hYX hx)
      · rintro (rfl | hx)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hx
    have hi : X ∩ insert e Y = Y := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, rfl | hy⟩
        · exact absurd hx heX
        · exact hy
      · intro hy
        exact ⟨hYX hy, Or.inr hy⟩
    rw [hu, hi] at hsub
    linarith

/-- The deletion marginals of `A` add up to at most `f(A) - f(∅)`; this is the
telescoping step behind (43). -/
theorem sum_deletion_le (f : Objective n) (A : Finset (Fin n)) :
    ∑ e ∈ A, (f.value A - f.value (A.erase e)) ≤ f.value A - f.value ∅ := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a B ha ih =>
    rw [Finset.sum_insert ha, Finset.erase_insert ha]
    have hterm : ∀ e ∈ B, f.value (insert a B) - f.value ((insert a B).erase e) ≤
        f.value B - f.value (B.erase e) := by
      intro e he
      have hsub : B.erase e ⊆ (insert a B).erase e :=
        Finset.erase_subset_erase e (Finset.subset_insert a B)
      have h := marginal_le f hsub e
      rwa [Finset.insert_erase (Finset.mem_insert_of_mem he), Finset.insert_erase he] at h
    have hsum := Finset.sum_le_sum hterm
    linarith

/-- Some element of a nonempty set `A` costs at most `f(A)/|A|` when deleted. -/
theorem exists_cheap_deletion (f : Objective n) {A : Finset (Fin n)} (hA : A.Nonempty) :
    ∃ e ∈ A, (A.card : ℝ) * (f.value A - f.value (A.erase e)) ≤ f.value A := by
  have hsum := sum_deletion_le f A
  have h0 := f.nonnegative ∅
  have hle : ∑ e ∈ A, (A.card : ℝ) * (f.value A - f.value (A.erase e)) ≤
      ∑ _e ∈ A, f.value A := by
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    nlinarith
  exact Finset.exists_le_of_sum_le hA hle

/-- The thinning inequality (43) with a general size: a set `A` with `m`
elements has a subset `T` with `r ≤ m` elements and `m f(T) ≥ r f(A)`, by
repeated deletion of a cheap element. -/
theorem exists_subset_ratio (f : Objective n) :
    ∀ (m : ℕ) (A : Finset (Fin n)), A.card = m → ∀ r ≤ m,
      ∃ T ⊆ A, T.card = r ∧ (r : ℝ) * f.value A ≤ m * f.value T := by
  intro m
  induction m with
  | zero =>
    intro A hA r hr
    refine ⟨A, Finset.Subset.refl A, by omega, ?_⟩
    have : r = 0 := by omega
    subst this
    simp
  | succ m ih =>
    intro A hA r hr
    rcases Nat.lt_or_ge r (m + 1) with hr' | hr'
    · have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e, he, hcheap⟩ := exists_cheap_deletion f hne
      have hcard : (A.erase e).card = m := by rw [Finset.card_erase_of_mem he, hA]; rfl
      obtain ⟨T, hT, hTcard, hTval⟩ := ih (A.erase e) hcard r (by omega)
      refine ⟨T, hT.trans (Finset.erase_subset e A), hTcard, ?_⟩
      rw [hA] at hcheap
      push_cast at hcheap ⊢
      have hfT := f.nonnegative T
      have hfA := f.nonnegative A
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : r = 0 := by omega
        subst this
        simp only [CharP.cast_eq_zero, zero_mul, zero_add, one_mul]
        exact hfT
      · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hrR : (r : ℝ) ≤ m := by exact_mod_cast (show r ≤ m by omega)
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        -- `m f(A) ≤ (m+1) f(A \ e)` and `r f(A \ e) ≤ m f(T)`.
        have h1 : (m : ℝ) * f.value A ≤ (m + 1) * f.value (A.erase e) := by linarith
        have h2 : (m : ℝ) * ((r : ℝ) * f.value A) ≤ (m : ℝ) * ((m + 1) * f.value T) := by
          calc (m : ℝ) * ((r : ℝ) * f.value A) = r * (m * f.value A) := by ring
            _ ≤ r * ((m + 1) * f.value (A.erase e)) := mul_le_mul_of_nonneg_left h1 hr0
            _ = (m + 1) * (r * f.value (A.erase e)) := by ring
            _ ≤ (m + 1) * (m * f.value T) := by
                apply mul_le_mul_of_nonneg_left hTval
                positivity
            _ = (m : ℝ) * ((m + 1) * f.value T) := by ring
        exact le_of_mul_le_mul_left h2 hmR
    · have : r = m + 1 := by omega
      subst this
      exact ⟨A, Finset.Subset.refl A, hA, le_refl _⟩

/-- `f(OPT^(κ)) ≥ (κ/k) f(A)`: every set of at most `k` elements has a subset of
at most `κ ≤ k` elements keeping a `κ/k` fraction of its value. -/
theorem exists_subset_fraction (f : Objective n) {A : Finset (Fin n)} {κ k : ℕ}
    (hA : A.card ≤ k) (hκ : κ ≤ k) (hk : 0 < k) :
    ∃ T ⊆ A, T.card ≤ κ ∧ (κ : ℝ) / k * f.value A ≤ f.value T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hfA := f.nonnegative A
  rcases le_or_gt A.card κ with hAκ | hAκ
  · refine ⟨A, Finset.Subset.refl A, hAκ, ?_⟩
    have : (κ : ℝ) / k ≤ 1 := (div_le_one hkR).mpr (by exact_mod_cast hκ)
    nlinarith
  · obtain ⟨T, hT, hTcard, hTval⟩ := exists_subset_ratio f A.card A rfl κ hAκ.le
    refine ⟨T, hT, hTcard.le, ?_⟩
    have hm : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
    have hmk : (A.card : ℝ) ≤ k := by exact_mod_cast hA
    have hfT := f.nonnegative T
    rw [div_mul_eq_mul_div, div_le_iff₀ hkR]
    nlinarith

/-! ### The instance at a checkpoint -/

/-- The future prefix `{x_{c+1}, ..., x_{c+j}}` after time `c`. -/
def future (n c j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun e : Fin n => c ≤ e.val ∧ e.val < c + j)

theorem exists_optimalCore (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) :
    ∃ O, O ⊆ P ∧ O.card ≤ κ ∧
      ∀ O', O' ⊆ P → O'.card ≤ κ → f.value (O' ∪ R) ≤ f.value (O ∪ R) := by
  classical
  obtain ⟨O, hO, hmax⟩ := (P.powerset.filter (fun O => O.card ≤ κ)).exists_max_image
    (fun O => f.value (O ∪ R)) ⟨∅, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_powerset] at hO hmax
  exact ⟨O, hO.1, hO.2, fun O' h1 h2 => hmax O' ⟨h1, h2⟩⟩

/-- A set of at most `κ` elements of `P` maximizing `f(O ∪ R)`. -/
def optimalCore (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) : Finset (Fin n) :=
  Classical.choose (exists_optimalCore f P R κ)

theorem optimalCore_spec (f : Objective n) (P R : Finset (Fin n)) (κ : ℕ) :
    optimalCore f P R κ ⊆ P ∧ (optimalCore f P R κ).card ≤ κ ∧
      ∀ O', O' ⊆ P → O'.card ≤ κ → f.value (O' ∪ R) ≤ f.value (optimalCore f P R κ ∪ R) :=
  Classical.choose_spec (exists_optimalCore f P R κ)

/-- The instance of the clairvoyant addition-robust problem at the checkpoint
`c`: `V_now = X_c`, budget `κ`, and `V_future = (x_{c+1}, ..., x_n)`, with one
future element per stage. -/
def window (f : Objective n) (κ c : ℕ) : WindowInstance n where
  objective := f
  present := arrivedPrefix n c
  coreBudget := κ
  lastStage := n - c
  arrivals j := future n c j.val
  candidate j := optimalCore f (arrivedPrefix n c) (future n c j.val) κ
  arrivals_zero := by
    ext e
    simp [future]
  arrivals_mono := by
    intro i j hij e he
    simp only [future, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have : i.val ≤ j.val := hij
    omega
  arrivals_disjoint := by
    intro j
    rw [Finset.disjoint_left]
    intro e he he'
    simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
    omega
  candidate_subset j := (optimalCore_spec _ _ _ _).1
  candidate_card j := (optimalCore_spec _ _ _ _).2.1
  candidate_optimal j O hO hcard := (optimalCore_spec _ _ _ _).2.2 O hO hcard

theorem window_singleArrivals (f : Objective n) (κ c : ℕ) : (window f κ c).SingleArrivals := by
  intro j
  have hj : c + j.val < n := by
    have := j.isLt
    change j.val < n - c at this
    omega
  refine ⟨⟨c + j.val, hj⟩, ?_, ?_⟩
  · simp [window, future]
  · ext e
    simp only [window, future, Fin.val_succ, Fin.val_castSucc, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro he
      by_cases hc : e.val = c + j.val
      · exact Or.inl (Fin.ext hc)
      · exact Or.inr ⟨he.1, by omega⟩
    · rintro (rfl | he)
      · exact ⟨by simp, by simp⟩
      · exact ⟨he.1, by omega⟩

/-- Every set of at most `κ` elements arrived by time `c + j` is worth at most the
benchmark `f(O_j ∪ R_j)` of the checkpoint instance at `c`. -/
theorem le_benchmark (f : Objective n) (κ c : ℕ) (j : Fin ((window f κ c).lastStage + 1))
    {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (c + j.val)) (hcard : T.card ≤ κ) :
    f.value T ≤ (window f κ c).benchmark j := by
  classical
  have hsplit : T ⊆ (T ∩ arrivedPrefix n c) ∪ future n c j.val := by
    intro e he
    have he' := hT he
    simp only [arrivedPrefix, future, Finset.mem_union, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at he' ⊢
    by_cases hc : e.val < c
    · exact Or.inl ⟨he, hc⟩
    · exact Or.inr ⟨by omega, he'⟩
  have hmono := f.monotone _ _ hsplit
  have hopt := (window f κ c).candidate_optimal j (T ∩ arrivedPrefix n c)
    Finset.inter_subset_right ((Finset.card_le_card Finset.inter_subset_left).trans hcard)
  exact hmono.trans hopt

/-- The addition-robust guarantee at the checkpoint `c`, against every set of at
most `κ` elements arrived by time `c + j`. -/
theorem robust_le {f : Objective n} {κ c : ℕ} {α : ℝ} (hα : 0 ≤ α)
    {w : Finset (Fin n) → ℝ} (hw : (window f κ c).IsAdditionRobust α w) {j : ℕ}
    (hj : j ≤ n - c) {T : Finset (Fin n)} (hT : T ⊆ arrivedPrefix n (c + j))
    (hcard : T.card ≤ κ) :
    α * f.value T ≤ ∑ S, w S * f.value (S ∪ future n c j) := by
  have hb := le_benchmark f κ c ⟨j, Nat.lt_succ_of_le hj⟩ hT hcard
  have hr := hw.2.2.2 ⟨j, Nat.lt_succ_of_le hj⟩
  exact (mul_le_mul_of_nonneg_left hb hα).trans hr

end ConsistentSubmodular.Checkpoints
