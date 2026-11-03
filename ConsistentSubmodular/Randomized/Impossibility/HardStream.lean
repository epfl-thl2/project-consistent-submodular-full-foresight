module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# The coverage stream of Theorem 1

The weighted coverage instance of Section 2.1 (Figure 2) and of the paragraph
"The instance" in Appendix A.2. The universe consists of three groups
`U₀, U₁, U₂` of `k` cells each, and a cell of group `g` has weight `u_g`. The
stream presents the `3k` singleton sets (the *tiny* sets below), the set of
group `g` and cell `b` at position `g k + b`, then `U₀`, which covers group `0`,
and finally `U₁`, which covers group `1`. The weighted coverage
`weightedValue k u T` of a family `T` is the total weight of the cells it
covers.

For natural weights `w_g ≤ W₀`, the unweighted stream `streamCover k W₀ w`
replaces every cell of group `g` by `w_g` unit-weight copies, so its coverage
is the weighted coverage with the weights `w_g` (`coverage_streamCover`); this
is the last step of "Removing the weights" in Appendix A.2.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace ConsistentSubmodular.HardInstance

/-- The cells `(g, b)` covered by a stream element: the tiny set at position
`g k + b < 3k` covers block `b` of group `g`, `U₀` (position `3k`) covers group
`0`, and `U₁` (position `3k + 1`) covers group `1`. -/
def elementCells (k : ℕ) (e : Fin (3 * k + 2)) : Finset (Fin 3 × Fin k) :=
  univ.filter fun c =>
    if e.val < 3 * k then c.1.val = e.val / k ∧ c.2.val = e.val % k
    else if e.val = 3 * k then c.1.val = 0 else c.1.val = 1

/-- The universe elements of a set of cells: the first `w g` of the `W₀`
copies of every cell of group `g`. -/
def cellSet (k W₀ : ℕ) (w : Fin 3 → ℕ) (B : Finset (Fin 3 × Fin k)) :
    Finset (Fin 3 × Fin k × Fin W₀) :=
  univ.filter fun x => (x.1, x.2.1) ∈ B ∧ x.2.2.val < w x.1

theorem card_cellSet {k W₀ : ℕ} {w : Fin 3 → ℕ} (hw : ∀ g, w g ≤ W₀)
    (B : Finset (Fin 3 × Fin k)) : (cellSet k W₀ w B).card = ∑ c ∈ B, w c.1 := by
  rw [cellSet, card_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hinner (g : Fin 3) (b : Fin k) :
      (∑ r : Fin W₀, if (g, b) ∈ B ∧ r.val < w g then 1 else 0) =
        if (g, b) ∈ B then w g else 0 := by
    by_cases hB : (g, b) ∈ B
    · simp only [hB, true_and, if_true]
      rw [← card_filter, Fin.card_filter_val_lt, min_eq_right (hw g)]
    · simp [hB]
  simp_rw [hinner]
  rw [← Fintype.sum_prod_type (fun c : Fin 3 × Fin k => if c ∈ B then w c.1 else 0),
    ← sum_filter]
  simp

theorem biUnion_cellSet {k W₀ : ℕ} {w : Fin 3 → ℕ} {ι : Type*} (S : Finset ι)
    (cells : ι → Finset (Fin 3 × Fin k)) :
    S.biUnion (fun e => cellSet k W₀ w (cells e)) = cellSet k W₀ w (S.biUnion cells) := by
  ext x
  simp only [cellSet, mem_biUnion, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e, he, hx, hr⟩
    exact ⟨⟨e, he, hx⟩, hr⟩
  · rintro ⟨⟨e, he, hx⟩, hr⟩
    exact ⟨e, he, hx, hr⟩

/-- The fibre of a set of cells over group `g`. -/
def fiber {k : ℕ} (C : Finset (Fin 3 × Fin k)) (g : Fin 3) : Finset (Fin 3 × Fin k) :=
  C.filter fun c => c.1 = g

theorem sum_weight_eq_fibers {k : ℕ} (w : Fin 3 → ℕ) (C : Finset (Fin 3 × Fin k)) :
    ∑ c ∈ C, w c.1 = ∑ g, w g * (fiber C g).card := by
  rw [← Finset.sum_fiberwise C Prod.fst]
  refine sum_congr rfl fun g _ => ?_
  rw [fiber, sum_congr rfl (fun c hc => by rw [(mem_filter.mp hc).2]), sum_const, smul_eq_mul,
    mul_comm]

/-- A fibre has at most `k` cells. -/
theorem card_fiber_le {k : ℕ} (C : Finset (Fin 3 × Fin k)) (g : Fin 3) :
    (fiber C g).card ≤ k := by
  calc (fiber C g).card ≤ (univ : Finset (Fin k)).card := by
        refine card_le_card_of_injOn Prod.snd (fun _ _ => mem_univ _) ?_
        intro c hc c' hc' h
        have h1 := (mem_filter.mp (mem_coe.mp hc)).2
        have h2 := (mem_filter.mp (mem_coe.mp hc')).2
        exact Prod.ext (h1.trans h2.symm) h
    _ = k := by simp

/-- A fibre containing the blocks `b < m` of group `g` has at least `m` cells. -/
theorem le_card_fiber {k m : ℕ} (hm : m ≤ k) (C : Finset (Fin 3 × Fin k)) (g : Fin 3)
    (hC : ∀ b : Fin k, b.val < m → (g, b) ∈ C) : m ≤ (fiber C g).card := by
  calc m = ((univ : Finset (Fin k)).filter fun b => b.val < m).card := by
        rw [Fin.card_filter_val_lt, min_eq_right hm]
    _ ≤ (fiber C g).card := by
        refine card_le_card_of_injOn (fun b => (g, b)) ?_ ?_
        · intro b hb
          have hb' := (mem_filter.mp (mem_coe.mp hb)).2
          exact mem_coe.mpr (mem_filter.mpr ⟨hC b hb', rfl⟩)
        · intro b _ b' _ h
          exact (Prod.ext_iff.mp h).2

/-- The number `c_g(T)` of tiny sets of group `g` in `T`. -/
def tinyCount (k : ℕ) (g : Fin 3) (T : Finset (Fin (3 * k + 2))) : ℕ :=
  (T.filter fun e => e.val < 3 * k ∧ e.val / k = g.val).card

/-- The tiny set of cell `(g, b)`, at position `g k + b`. -/
def tinyAt {k : ℕ} (c : Fin 3 × Fin k) : Fin (3 * k + 2) :=
  ⟨c.1.val * k + c.2.val, by
    have h1 := c.1.isLt
    have h2 := c.2.isLt
    have h3 : c.1.val * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
    omega⟩

/-- Without the large set of group `g`, the cells of group `g` are covered by
tiny sets, one cell per set. -/
theorem card_fiber_le_tinyCount {k : ℕ} (S : Finset (Fin (3 * k + 2))) (g : Fin 3)
    (hfull : ∀ e ∈ S, e.val ≠ 3 * k + g.val) :
    (fiber (S.biUnion (elementCells k)) g).card ≤ tinyCount k g S := by
  refine card_le_card_of_injOn tinyAt ?_ ?_
  · intro c hc
    obtain ⟨hcS, hcg⟩ := mem_filter.mp (mem_coe.mp hc)
    obtain ⟨e, he, hce⟩ := mem_biUnion.mp hcS
    have hce' := (mem_filter.mp hce).2
    refine mem_coe.mpr (mem_filter.mpr ?_)
    by_cases hlt : e.val < 3 * k
    · rw [if_pos hlt] at hce'
      obtain ⟨h1, h2⟩ := hce'
      have hdiv := Nat.div_add_mod e.val k
      have heq : tinyAt c = e := by
        apply Fin.ext
        simp only [tinyAt]
        rw [h1, h2]
        linarith [Nat.mul_comm k (e.val / k)]
      rw [heq]
      exact ⟨he, hlt, by rw [← h1, hcg]⟩
    · rw [if_neg hlt] at hce'
      exfalso
      by_cases h3k : e.val = 3 * k
      · rw [if_pos h3k] at hce'
        exact hfull e he (by rw [h3k, ← hcg, hce']; rfl)
      · rw [if_neg h3k] at hce'
        have he2 := e.isLt
        exact hfull e he (by rw [← hcg, hce']; omega)
  · intro c hc c' hc' h
    have h1 := (mem_filter.mp (mem_coe.mp hc)).2
    have h2 := (mem_filter.mp (mem_coe.mp hc')).2
    have hv := congrArg Fin.val h
    simp only [tinyAt] at hv
    rw [h1, ← h2] at hv
    exact Prod.ext (h1.trans h2.symm) (Fin.ext (by omega))

/-- The tiny sets of the three groups are disjoint, so a family contains at
most as many tiny sets as elements. -/
theorem tinyCount_sum_le {k : ℕ} (T : Finset (Fin (3 * k + 2))) :
    tinyCount k 0 T + tinyCount k 1 T + tinyCount k 2 T ≤ T.card := by
  have hdisj (g h : Fin 3) (hgh : g ≠ h) :
      Disjoint (T.filter fun e => e.val < 3 * k ∧ e.val / k = g.val)
        (T.filter fun e => e.val < 3 * k ∧ e.val / k = h.val) := by
    rw [disjoint_filter]
    intro e _ hg hh
    exact hgh (Fin.ext (hg.2.symm.trans hh.2))
  unfold tinyCount
  rw [← card_union_of_disjoint (hdisj 0 1 (by decide)),
    ← card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩)]
  exact card_le_card (union_subset (union_subset (filter_subset _ _) (filter_subset _ _))
    (filter_subset _ _))

/-- A tiny set of `T'` is a tiny set of `T` or an insertion of `T' \ T`. -/
theorem tinyCount_le_add {k : ℕ} (T T' : Finset (Fin (3 * k + 2))) (g : Fin 3) :
    tinyCount k g T' ≤ tinyCount k g T + tinyCount k g (T' \ T) := by
  unfold tinyCount
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro e he
  obtain ⟨heT', hp⟩ := mem_filter.mp he
  by_cases heT : e ∈ T
  · exact mem_union_left _ (mem_filter.mpr ⟨heT, hp⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨heT', heT⟩, hp⟩)

/-- The insertions number at most the recourse. -/
theorem card_sdiff_le_recourse {n : ℕ} (T T' : Finset (Fin n)) : (T' \ T).card ≤ recourse T' T :=
  card_le_card subset_union_left

/-- The insertions of tiny sets of groups `1` and `2` number at most the recourse. -/
theorem tinyCount_sdiff_le {k : ℕ} (T T' : Finset (Fin (3 * k + 2))) :
    tinyCount k 1 (T' \ T) + tinyCount k 2 (T' \ T) ≤ recourse T' T := by
  refine le_trans ?_ (card_sdiff_le_recourse T T')
  unfold tinyCount
  rw [← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · rw [disjoint_filter]
    intro e _ h1 h2
    exact absurd (h1.2.symm.trans h2.2) (by decide)

/-- The weighted coverage `f_u(T)` of a family `T`: the total weight of the cells
it covers, where every cell of group `g` has weight `u g`. -/
def weightedValue (k : ℕ) (u : Fin 3 → ℝ) (T : Finset (Fin (3 * k + 2))) : ℝ :=
  ∑ g, u g * (fiber (T.biUnion (elementCells k)) g).card

/-- The cover of the stream, with the universe `Fin 3 × Fin k × Fin W₀` encoded
as `Fin u`. -/
def streamCover (k W₀ : ℕ) (w : Fin 3 → ℕ) (e : Fin (3 * k + 2)) :
    Finset (Fin (Fintype.card (Fin 3 × Fin k × Fin W₀))) :=
  (cellSet k W₀ w (elementCells k e)).map (Fintype.equivFin _).toEmbedding

/-- Unit-weight copies realize natural weights: the coverage of a family is its
weighted coverage with the weights `w g`. -/
theorem coverage_streamCover {k W₀ : ℕ} {w : Fin 3 → ℕ} (hw : ∀ g, w g ≤ W₀)
    (S : Finset (Fin (3 * k + 2))) :
    coverageValue (streamCover k W₀ w) S = weightedValue k (fun g => (w g : ℝ)) S := by
  have h : S.biUnion (streamCover k W₀ w) =
      (cellSet k W₀ w (S.biUnion (elementCells k))).map (Fintype.equivFin _).toEmbedding := by
    have hdef : streamCover k W₀ w =
        fun e => (cellSet k W₀ w (elementCells k e)).map (Fintype.equivFin _).toEmbedding := rfl
    rw [hdef, ← biUnion_cellSet]
    simp only [map_eq_image]
    rw [biUnion_image]
  rw [coverageValue, h, card_map, card_cellSet hw, sum_weight_eq_fibers]
  push_cast
  rfl

/-- `U₀`, the large set of group `0`, at position `3k`. -/
def bigZero (k : ℕ) : Fin (3 * k + 2) := ⟨3 * k, by omega⟩

/-- `U₁`, the large set of group `1`, at position `3k + 1`. -/
def bigOne (k : ℕ) : Fin (3 * k + 2) := ⟨3 * k + 1, by omega⟩

theorem mem_elementCells_tinyAt {k : ℕ} (c : Fin 3 × Fin k) : c ∈ elementCells k (tinyAt c) := by
  have hk : 0 < k := Nat.pos_of_ne_zero fun h => by subst h; exact c.2.elim0
  have hb := c.2.isLt
  have hg := c.1.isLt
  have h3 : c.1.val * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
  have hdiv : (c.2.val + c.1.val * k) / k = c.1.val := by
    rw [Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hb, zero_add]
  have hmod : (c.2.val + c.1.val * k) % k = c.2.val := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  simp only [elementCells, tinyAt, mem_filter, mem_univ, true_and]
  rw [if_pos (by omega), Nat.add_comm (c.1.val * k), hdiv, hmod]
  exact ⟨rfl, rfl⟩

theorem mem_elementCells_bigZero {k : ℕ} (b : Fin k) : ((0 : Fin 3), b) ∈ elementCells k (bigZero k) := by
  simp only [elementCells, bigZero, mem_filter, mem_univ, true_and]
  rw [if_neg (by omega)]
  simp

theorem mem_elementCells_bigOne {k : ℕ} (b : Fin k) : ((1 : Fin 3), b) ∈ elementCells k (bigOne k) := by
  simp only [elementCells, bigOne, mem_filter, mem_univ, true_and]
  rw [if_neg (by omega), if_neg (by omega)]
  simp

section Bounds

variable {k : ℕ} {u : Fin 3 → ℝ}

/-- A family covering at least `n_g` cells of every group `g` has weighted
coverage at least `Σ_g u_g n_g`. -/
theorem le_weightedValue (hu : ∀ g, 0 ≤ u g) (T : Finset (Fin (3 * k + 2))) {n₀ n₁ n₂ : ℝ}
    (h₀ : n₀ ≤ (fiber (T.biUnion (elementCells k)) 0).card)
    (h₁ : n₁ ≤ (fiber (T.biUnion (elementCells k)) 1).card)
    (h₂ : n₂ ≤ (fiber (T.biUnion (elementCells k)) 2).card) :
    u 0 * n₀ + u 1 * n₁ + u 2 * n₂ ≤ weightedValue k u T := by
  rw [weightedValue, Fin.sum_univ_three]
  have := mul_le_mul_of_nonneg_left h₀ (hu 0)
  have := mul_le_mul_of_nonneg_left h₁ (hu 1)
  have := mul_le_mul_of_nonneg_left h₂ (hu 2)
  linarith

/-- Before `U₀` arrives, a family of tiny sets covers at most `Σ_g u_g c_g`. -/
theorem value_le_before (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2)))
    (hS : ∀ e ∈ S, e.val < 3 * k) :
    weightedValue k u S ≤
      u 0 * tinyCount k 0 S + u 1 * tinyCount k 1 S + u 2 * tinyCount k 2 S := by
  rw [weightedValue, Fin.sum_univ_three]
  have h0 : ((fiber (S.biUnion (elementCells k)) 0).card : ℝ) ≤ tinyCount k 0 S := by
    exact_mod_cast card_fiber_le_tinyCount S 0 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 0
      omega
  have h1 : ((fiber (S.biUnion (elementCells k)) 1).card : ℝ) ≤ tinyCount k 1 S := by
    exact_mod_cast card_fiber_le_tinyCount S 1 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 1
      omega
  have h2 : ((fiber (S.biUnion (elementCells k)) 2).card : ℝ) ≤ tinyCount k 2 S := by
    exact_mod_cast card_fiber_le_tinyCount S 2 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 2
      omega
  have := mul_le_mul_of_nonneg_left h0 (hu 0)
  have := mul_le_mul_of_nonneg_left h1 (hu 1)
  have := mul_le_mul_of_nonneg_left h2 (hu 2)
  linarith

/-- Before `U₁` arrives, group `0` contributes at most `k u₀`. -/
theorem value_le_middle (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2)))
    (hS : ∀ e ∈ S, e.val < 3 * k + 1) :
    weightedValue k u S ≤ u 0 * k + u 1 * tinyCount k 1 S + u 2 * tinyCount k 2 S := by
  rw [weightedValue, Fin.sum_univ_three]
  have h0 : ((fiber (S.biUnion (elementCells k)) 0).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (S.biUnion (elementCells k)) 0
  have h1 : ((fiber (S.biUnion (elementCells k)) 1).card : ℝ) ≤ tinyCount k 1 S := by
    exact_mod_cast card_fiber_le_tinyCount S 1 fun e he => by
      have := hS e he
      change e.val ≠ 3 * k + 1
      omega
  have h2 : ((fiber (S.biUnion (elementCells k)) 2).card : ℝ) ≤ tinyCount k 2 S := by
    exact_mod_cast card_fiber_le_tinyCount S 2 fun e he => by
      have := e.isLt
      change e.val ≠ 3 * k + 2
      omega
  have := mul_le_mul_of_nonneg_left h0 (hu 0)
  have := mul_le_mul_of_nonneg_left h1 (hu 1)
  have := mul_le_mul_of_nonneg_left h2 (hu 2)
  linarith

/-- At the end, groups `0` and `1` contribute at most `k u₀ + k u₁`. -/
theorem value_le_after (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2))) :
    weightedValue k u S ≤ u 0 * k + u 1 * k + u 2 * tinyCount k 2 S := by
  rw [weightedValue, Fin.sum_univ_three]
  have h0 : ((fiber (S.biUnion (elementCells k)) 0).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (S.biUnion (elementCells k)) 0
  have h1 : ((fiber (S.biUnion (elementCells k)) 1).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (S.biUnion (elementCells k)) 1
  have h2 : ((fiber (S.biUnion (elementCells k)) 2).card : ℝ) ≤ tinyCount k 2 S := by
    exact_mod_cast card_fiber_le_tinyCount S 2 fun e he => by
      have := e.isLt
      change e.val ≠ 3 * k + 2
      omega
  have := mul_le_mul_of_nonneg_left h0 (hu 0)
  have := mul_le_mul_of_nonneg_left h1 (hu 1)
  have := mul_le_mul_of_nonneg_left h2 (hu 2)
  linarith

/-- Changing the weights of groups `1` and `2` by at most `δ` changes the
weighted coverage of a family by at most `2 δ k`: the family covers at most
`k` cells of each group. -/
theorem abs_weightedValue_sub_le {v : Fin 3 → ℝ} {δ : ℝ} (h0 : v 0 = u 0)
    (h1 : |v 1 - u 1| ≤ δ) (h2 : |v 2 - u 2| ≤ δ) (T : Finset (Fin (3 * k + 2))) :
    |weightedValue k v T - weightedValue k u T| ≤ 2 * δ * k := by
  have hc₁ : ((fiber (T.biUnion (elementCells k)) 1).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (T.biUnion (elementCells k)) 1
  have hc₂ : ((fiber (T.biUnion (elementCells k)) 2).card : ℝ) ≤ k := by
    exact_mod_cast card_fiber_le (T.biUnion (elementCells k)) 2
  set c₁ : ℝ := ((fiber (T.biUnion (elementCells k)) 1).card : ℝ)
  set c₂ : ℝ := ((fiber (T.biUnion (elementCells k)) 2).card : ℝ)
  have hdiff : weightedValue k v T - weightedValue k u T = (v 1 - u 1) * c₁ + (v 2 - u 2) * c₂ := by
    simp only [weightedValue, Fin.sum_univ_three, h0, c₁, c₂]
    ring
  have hc₁0 : 0 ≤ c₁ := Nat.cast_nonneg _
  have hc₂0 : 0 ≤ c₂ := Nat.cast_nonneg _
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h1
  rw [hdiff]
  calc |(v 1 - u 1) * c₁ + (v 2 - u 2) * c₂|
      ≤ |(v 1 - u 1) * c₁| + |(v 2 - u 2) * c₂| := abs_add_le _ _
    _ = |v 1 - u 1| * c₁ + |v 2 - u 2| * c₂ := by
        rw [abs_mul, abs_mul, abs_of_nonneg hc₁0, abs_of_nonneg hc₂0]
    _ ≤ δ * k + δ * k :=
        add_le_add (mul_le_mul h1 hc₁ hc₁0 hδ) (mul_le_mul h2 hc₂ hc₂0 hδ)
    _ = 2 * δ * k := by ring

end Bounds

/-- The positions `a, ..., a + m - 1` of the stream. -/
def positions (k a m : ℕ) : Finset (Fin (3 * k + 2)) :=
  univ.filter fun e => a ≤ e.val ∧ e.val < a + m

theorem card_positions_le (k a m : ℕ) : (positions k a m).card ≤ m := by
  calc (positions k a m).card ≤ (range m).card := by
        refine card_le_card_of_injOn (fun e => e.val - a) ?_ ?_
        · intro e he
          have := (mem_filter.mp (mem_coe.mp he)).2
          exact mem_coe.mpr (mem_range.mpr (show e.val - a < m by omega))
        · intro e he e' he' h
          have h1 := (mem_filter.mp (mem_coe.mp he)).2
          have h2 := (mem_filter.mp (mem_coe.mp he')).2
          have h' : e.val - a = e'.val - a := h
          exact Fin.ext (by omega)
    _ = m := card_range m

/-- The competitor before `U₀` arrives: the `k` tiny sets of group `0`. -/
def firstCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) := positions k 0 k

/-- The competitor after `U₀` arrives: `U₀` and `k - 1` tiny sets of group `1`. -/
def secondCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) :=
  insert (bigZero k) (positions k k (k - 1))

/-- The competitor at the end: `U₀`, `U₁`, and `k - 2` tiny sets of group `2`. -/
def thirdCompetitor (k : ℕ) : Finset (Fin (3 * k + 2)) :=
  insert (bigZero k) (insert (bigOne k) (positions k (2 * k) (k - 2)))

section Competitors

variable {k : ℕ}

theorem tinyAt_mem_positions {a m : ℕ} (c : Fin 3 × Fin k) (h1 : a ≤ c.1.val * k + c.2.val)
    (h2 : c.1.val * k + c.2.val < a + m) : tinyAt c ∈ positions k a m :=
  mem_filter.mpr ⟨mem_univ _, h1, h2⟩

/-- The competitor before `U₀` arrives covers all cells of group `0`. -/
theorem firstCompetitor_fibers :
    k ≤ (fiber ((firstCompetitor k).biUnion (elementCells k)) 0).card :=
  le_card_fiber le_rfl _ 0 fun b _ => mem_biUnion.mpr ⟨tinyAt (0, b),
    tinyAt_mem_positions (0, b) (Nat.zero_le _) (by simp [b.isLt]), mem_elementCells_tinyAt _⟩

/-- The competitor after `U₀` arrives covers group `0` and `k - 1` cells of
group `1`. -/
theorem secondCompetitor_fibers :
    k ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 0).card ∧
      k - 1 ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 1).card := by
  refine ⟨le_card_fiber le_rfl _ 0 fun b _ =>
      mem_biUnion.mpr ⟨bigZero k, mem_insert_self _ _, mem_elementCells_bigZero b⟩, ?_⟩
  refine le_card_fiber (Nat.sub_le k 1) _ 1 fun b hb => mem_biUnion.mpr
    ⟨tinyAt (1, b), mem_insert_of_mem ?_, mem_elementCells_tinyAt _⟩
  exact tinyAt_mem_positions (1, b) (show k ≤ 1 * k + b.val by omega)
    (show 1 * k + b.val < k + (k - 1) by omega)

/-- The competitor at the end covers groups `0` and `1` and `k - 2` cells of
group `2`. -/
theorem thirdCompetitor_fibers :
    k ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 0).card ∧
      k ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 1).card ∧
      k - 2 ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 2).card := by
  refine ⟨le_card_fiber le_rfl _ 0 fun b _ =>
      mem_biUnion.mpr ⟨bigZero k, mem_insert_self _ _, mem_elementCells_bigZero b⟩,
    le_card_fiber le_rfl _ 1 fun b _ =>
      mem_biUnion.mpr ⟨bigOne k, mem_insert_of_mem (mem_insert_self _ _),
        mem_elementCells_bigOne b⟩, ?_⟩
  refine le_card_fiber (Nat.sub_le k 2) _ 2 fun b hb => mem_biUnion.mpr
    ⟨tinyAt (2, b), mem_insert_of_mem (mem_insert_of_mem ?_), mem_elementCells_tinyAt _⟩
  exact tinyAt_mem_positions (2, b) (show 2 * k ≤ 2 * k + b.val by omega)
    (show 2 * k + b.val < 2 * k + (k - 2) by omega)

variable {u : Fin 3 → ℝ}

/-- The optimum `o₀ = k u₀` before `U₀` arrives, as a lower bound. -/
theorem value_firstCompetitor (hu : ∀ g, 0 ≤ u g) :
    u 0 * k ≤ weightedValue k u (firstCompetitor k) := by
  have h := le_weightedValue hu (firstCompetitor k) (n₀ := k) (n₁ := 0) (n₂ := 0)
    (by exact_mod_cast firstCompetitor_fibers) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- The optimum `o₁ = k u₀ + (k - 1) u₁` after `U₀` arrives, as a lower bound. -/
theorem value_secondCompetitor (hu : ∀ g, 0 ≤ u g) (hk : 1 ≤ k) :
    u 0 * k + u 1 * ((k : ℝ) - 1) ≤ weightedValue k u (secondCompetitor k) := by
  obtain ⟨h0, h1⟩ := secondCompetitor_fibers (k := k)
  have h1' : (k : ℝ) - 1 ≤ (fiber ((secondCompetitor k).biUnion (elementCells k)) 1).card := by
    have := (Nat.cast_le (α := ℝ)).mpr h1
    rwa [Nat.cast_sub hk, Nat.cast_one] at this
  have h := le_weightedValue hu (secondCompetitor k) (n₀ := k) (n₂ := 0) (by exact_mod_cast h0) h1'
    (Nat.cast_nonneg _)
  linarith

/-- The optimum `o₂ = k u₀ + k u₁ + (k - 2) u₂` at the end, as a lower bound. -/
theorem value_thirdCompetitor (hu : ∀ g, 0 ≤ u g) (hk : 2 ≤ k) :
    u 0 * k + u 1 * k + u 2 * ((k : ℝ) - 2) ≤ weightedValue k u (thirdCompetitor k) := by
  obtain ⟨h0, h1, h2⟩ := thirdCompetitor_fibers (k := k)
  have h2' : (k : ℝ) - 2 ≤ (fiber ((thirdCompetitor k).biUnion (elementCells k)) 2).card := by
    have := (Nat.cast_le (α := ℝ)).mpr h2
    rwa [Nat.cast_sub hk, Nat.cast_ofNat] at this
  exact le_weightedValue hu (thirdCompetitor k) (n₀ := k) (n₁ := k) (by exact_mod_cast h0)
    (by exact_mod_cast h1) h2'

theorem card_firstCompetitor_le : (firstCompetitor k).card ≤ k := card_positions_le k 0 k

theorem card_secondCompetitor_le (hk : 1 ≤ k) : (secondCompetitor k).card ≤ k := by
  have := card_insert_le (bigZero k) (positions k k (k - 1))
  have := card_positions_le k k (k - 1)
  unfold secondCompetitor
  omega

theorem card_thirdCompetitor_le (hk : 2 ≤ k) : (thirdCompetitor k).card ≤ k := by
  have := card_insert_le (bigZero k) (insert (bigOne k) (positions k (2 * k) (k - 2)))
  have := card_insert_le (bigOne k) (positions k (2 * k) (k - 2))
  have := card_positions_le k (2 * k) (k - 2)
  unfold thirdCompetitor
  omega

theorem firstCompetitor_arrived : firstCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k) := by
  intro e he
  have := (mem_filter.mp he).2
  exact mem_filter.mpr ⟨mem_univ _, by omega⟩

theorem secondCompetitor_arrived : secondCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k + 1) := by
  intro e he
  rcases mem_insert.mp he with rfl | he
  · exact mem_filter.mpr ⟨mem_univ _, show 3 * k < 3 * k + 1 by omega⟩
  · have := (mem_filter.mp he).2
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩

theorem thirdCompetitor_arrived : thirdCompetitor k ⊆ arrivedPrefix (3 * k + 2) (3 * k + 2) :=
  fun e _ => mem_filter.mpr ⟨mem_univ _, e.isLt⟩

end Competitors

end ConsistentSubmodular.HardInstance
