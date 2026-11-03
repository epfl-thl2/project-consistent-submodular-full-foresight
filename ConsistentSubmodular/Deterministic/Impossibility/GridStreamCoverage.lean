module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# Coverage on the stream `Σ` of Appendix B.1

Counting lemmas for `gridStreamCover k m`, the stream `Σ` of Appendix B.1.1.
A set with `n` rows and `c` column sets, all from the stages up to `j`, covers
at most `n k + c (k - n) + c j` elements (`card_cover_le`): the rows cover
`n k` grid cells, each column set adds at most the `k - n` cells of its column
outside these rows, and at most `j` auxiliary elements. With `c ≤ k - n` this
is the bound `n k + (k - n)(k + j) - n (k - n)` of Appendix B.1.2
(`coverage_le`), which the paper obtains instead by replacing the column sets
with distinct columns of `B_j`. The `k` rows cover the whole grid
(`coverage_rows`), and the `k` columns of stage `j` cover the grid and `j`
auxiliary elements each (`coverage_stage`): `|b_{i,j}| = k + j`, so `B_j`
covers `k² + k j` elements.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace ConsistentSubmodular.GridStream

/-- The number of column sets `b_{i,j}` in `S`. -/
def columnsHeld (k : ℕ) {N : ℕ} (S : Finset (Fin N)) : ℕ :=
  (S.filter fun e => k ≤ e.val).card

theorem rowsHeld_add_columnsHeld (k : ℕ) {N : ℕ} (S : Finset (Fin N)) :
    rowsHeld k S + columnsHeld k S = S.card := by
  have h := card_filter_add_card_filter_not (s := S) (fun e : Fin N => e.val < k)
  have hnot : S.filter (fun e => ¬ e.val < k) = S.filter (fun e => k ≤ e.val) := by
    ext e
    simp [not_lt]
  rw [hnot] at h
  exact h

/-- Rows enter and leave one at a time: `n_t` changes by at most the recourse. -/
theorem rowsHeld_le_add_recourse (k : ℕ) {N : ℕ} (A B : Finset (Fin N)) :
    rowsHeld k B ≤ rowsHeld k A + recourse A B := by
  classical
  unfold rowsHeld recourse
  have hsub : B.filter (fun e => e.val < k) ⊆ A.filter (fun e => e.val < k) ∪ (B \ A) := by
    intro e he
    obtain ⟨heB, hek⟩ := mem_filter.mp he
    by_cases heA : e ∈ A
    · exact mem_union_left _ (mem_filter.mpr ⟨heA, hek⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨heB, heA⟩)
  calc (B.filter fun e => e.val < k).card
      ≤ ((A.filter fun e => e.val < k) ∪ (B \ A)).card := card_le_card hsub
    _ ≤ (A.filter fun e => e.val < k).card + (B \ A).card := card_union_le _ _
    _ ≤ (A.filter fun e => e.val < k).card + ((A \ B) ∪ (B \ A)).card := by
        gcongr
        exact subset_union_right

theorem rowsHeld_le_card (k : ℕ) {N : ℕ} (S : Finset (Fin N)) : rowsHeld k S ≤ S.card :=
  card_filter_le _ _

theorem card_arrivedPrefix {n t : ℕ} (h : t ≤ n) : (arrivedPrefix n t).card = t := by
  have hmap : (arrivedPrefix n t).map Fin.valEmbedding = range t := by
    ext x
    simp only [arrivedPrefix, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, hmap, card_range]

theorem arrivedPrefix_mono {n a b : ℕ} (h : a ≤ b) : arrivedPrefix n a ⊆ arrivedPrefix n b := by
  intro e he
  simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at he ⊢
  omega

theorem coverage_mono {n u : ℕ} (cover : Fin n → Finset (Fin u)) {A B : Finset (Fin n)}
    (h : A ⊆ B) : coverageValue cover A ≤ coverageValue cover B := by
  unfold coverageValue
  exact_mod_cast card_le_card (biUnion_subset_biUnion_of_subset_left _ h)

theorem coverage_nonneg {n u : ℕ} (cover : Fin n → Finset (Fin u)) (A : Finset (Fin n)) :
    0 ≤ coverageValue cover A :=
  Nat.cast_nonneg _

/-- Division with remainder for `a n + b` with `b < n`. -/
theorem mul_add_div_mod {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le b) hb
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- A column set present at time `t` is from a stage at most `(t - 1) / k`: the
set `b_{i,j}` sits at the position `j k + i - 1 < t`, and its stage index in the
cover is `(e - k) / k = j - 1`. -/
theorem stage_lt_of_arrived {k N t : ℕ} (hk : 0 < k) {S : Finset (Fin N)}
    (hS : S ⊆ arrivedPrefix N t) : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < (t - 1) / k := by
  intro e he hke
  have het : e.val < t := by
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    exact this
  have h1 : (e.val - k) / k + 1 = e.val / k := by
    rw [← Nat.add_div_right _ hk, Nat.sub_add_cancel hke]
  have h2 : e.val / k ≤ (t - 1) / k := Nat.div_le_div_right (by omega)
  omega

/-- A set with `n` rows and `c` column sets from the stages up to `j` covers at
most `n k + c (k - n) + c j` elements. The covered grid cells lie in the `n`
rows or, outside them, in the at most `c` columns of the column sets; the
auxiliary elements of column `i` that are covered are among
`u_{i,1}, ..., u_{i,j}`. -/
theorem card_cover_le {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    (S.biUnion (gridStreamCover k m)).card ≤
      rowsHeld k S * k + columnsHeld k S * (k - rowsHeld k S) + columnsHeld k S * j := by
  classical
  set Rs : Finset ℕ := (S.filter fun e => e.val < k).image Fin.val with hRs
  set Is : Finset ℕ := (S.filter fun e => k ≤ e.val).image fun e => (e.val - k) % k with hIs
  have hRcard : Rs.card = rowsHeld k S := card_image_of_injective _ Fin.val_injective
  have hIcard : Is.card ≤ columnsHeld k S := card_image_le
  have hRsub : Rs ⊆ range k := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := mem_image.mp hr
    exact mem_range.mpr (mem_filter.mp he).2
  have hsub : (S.biUnion (gridStreamCover k m)).map Fin.valEmbedding ⊆
      ((Rs ×ˢ range k).image fun p => p.1 * k + p.2) ∪
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2) ∪
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    obtain ⟨e, he, hxe⟩ := mem_biUnion.mp hx
    simp only [gridStreamCover, mem_filter, mem_univ, true_and] at hxe
    simp only [Fin.valEmbedding_apply]
    split_ifs at hxe with hrow
    · -- a cell of the row `a_{e+1}`
      obtain ⟨_, hdiv⟩ := hxe
      have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hrow
      refine mem_union_left _ (mem_union_left _ (mem_image.mpr
        ⟨(x.val / k, x.val % k), mem_product.mpr ⟨?_, mem_range.mpr (Nat.mod_lt _ hk)⟩,
          Nat.div_add_mod' x.val k⟩))
      rw [hdiv]
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨he, hrow⟩, rfl⟩
    · have hi : (e.val - k) % k ∈ Is :=
        mem_image.mpr ⟨e, mem_filter.mpr ⟨he, by omega⟩, rfl⟩
      rcases hxe with ⟨hxk, hmod⟩ | ⟨hxk, hdiv, hlt⟩
      · -- a grid cell of the column of `e`, inside a held row or not
        have hk : 0 < k := by
          rcases Nat.eq_zero_or_pos k with h | h
          · subst h
            simp at hxk
          · exact h
        have hr : x.val / k < k := (Nat.div_lt_iff_lt_mul hk).mpr hxk
        by_cases hrR : x.val / k ∈ Rs
        · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨(x.val / k, x.val % k),
            mem_product.mpr ⟨hrR, mem_range.mpr (Nat.mod_lt _ hk)⟩, Nat.div_add_mod' x.val k⟩))
        · refine mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨(x.val / k, x.val % k),
            mem_product.mpr ⟨mem_sdiff.mpr ⟨mem_range.mpr hr, hrR⟩, ?_⟩,
              Nat.div_add_mod' x.val k⟩))
          rw [hmod]
          exact hi
      · -- an auxiliary element `u_{i,l+1}` with `l ≤ (e - k) / k < j`
        refine mem_union_right _ (mem_image.mpr ⟨((x.val - k * k) / m, (x.val - k * k) % m),
          mem_product.mpr ⟨by rw [hdiv]; exact hi, mem_range.mpr ?_⟩, ?_⟩)
        · exact lt_of_le_of_lt hlt (hj e he (by omega))
        · have := Nat.div_add_mod' (x.val - k * k) m
          simp only
          omega
  have hprod1 : ((Rs ×ˢ range k).image fun p => p.1 * k + p.2).card ≤ Rs.card * k := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
  have hprod2 : (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2).card ≤
      (k - Rs.card) * Is.card := by
    refine card_image_le.trans ?_
    rw [card_product, card_sdiff_of_subset hRsub, card_range]
  have hprod3 : ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2).card ≤ Is.card * j := by
    refine card_image_le.trans ?_
    rw [card_product, card_range]
  have hunion : (((Rs ×ˢ range k).image fun p => p.1 * k + p.2) ∪
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2) ∪
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2)).card ≤
      ((Rs ×ˢ range k).image fun p => p.1 * k + p.2).card +
        (((range k \ Rs) ×ˢ Is).image fun p => p.1 * k + p.2).card +
        ((Is ×ˢ range j).image fun p => k * k + p.1 * m + p.2).card :=
    (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hmain := (card_le_card hsub).trans hunion
  rw [card_map] at hmain
  rw [hRcard] at hprod1 hprod2
  have h2 : (k - rowsHeld k S) * Is.card ≤ columnsHeld k S * (k - rowsHeld k S) := by
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hIcard
  have h3 : Is.card * j ≤ columnsHeld k S * j := Nat.mul_le_mul_right _ hIcard
  omega

/-- The coverage bound of Appendix B.1.2, used by Lemma 6 and Theorem 3: a set of
at most `k` stream sets with `n` rows and column sets from the stages up to `j`
covers at most `n k + (k - n)(k + j) - n (k - n)` elements. -/
theorem coverage_le {k m : ℕ} (S : Finset (Fin (k + m * k))) (j : ℕ) (hcard : S.card ≤ k)
    (hj : ∀ e ∈ S, k ≤ e.val → (e.val - k) / k < j) :
    coverageValue (gridStreamCover k m) S ≤
      (rowsHeld k S : ℝ) * k + ((k : ℝ) - rowsHeld k S) * (k + j) -
        rowsHeld k S * ((k : ℝ) - rowsHeld k S) := by
  have h := card_cover_le S j hj
  have hsum := rowsHeld_add_columnsHeld k S
  have hnk : rowsHeld k S ≤ k := by omega
  have hck : columnsHeld k S + rowsHeld k S ≤ k := by omega
  have hcR : ((columnsHeld k S : ℕ) : ℝ) + rowsHeld k S ≤ k := by exact_mod_cast hck
  have hR : coverageValue (gridStreamCover k m) S ≤
      (rowsHeld k S : ℝ) * k + (columnsHeld k S : ℝ) * ((k : ℝ) - rowsHeld k S) +
        (columnsHeld k S : ℝ) * j := by
    unfold coverageValue
    have hc := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub hnk] at hc
    exact hc
  have hkn : (0 : ℝ) ≤ (k : ℝ) - rowsHeld k S := by linarith [Nat.cast_nonneg (α := ℝ) (columnsHeld k S)]
  have hc1 : (columnsHeld k S : ℝ) ≤ (k : ℝ) - rowsHeld k S := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hc1 hkn, mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg (α := ℝ) j)]

/-- With no column sets, the rows held cover at most `n k` cells. -/
theorem coverage_le_rows {k m : ℕ} (S : Finset (Fin (k + m * k)))
    (hS : S ⊆ arrivedPrefix (k + m * k) k) :
    coverageValue (gridStreamCover k m) S ≤ (rowsHeld k S : ℝ) * k := by
  have hcol : columnsHeld k S = 0 := by
    unfold columnsHeld
    rw [card_eq_zero, filter_eq_empty_iff]
    intro e he
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    omega
  have h := card_cover_le (m := m) S 0 (fun e he hke => by
    have := hS he
    simp only [arrivedPrefix, mem_filter, mem_univ, true_and] at this
    omega)
  rw [hcol] at h
  unfold coverageValue
  have hc := (Nat.cast_le (α := ℝ)).mpr h
  push_cast at hc
  simpa using hc

/-- The `k` rows `a_1, ..., a_k` cover the whole grid `U_core`. -/
theorem coverage_rows {k m : ℕ} :
    (k : ℝ) * k ≤ coverageValue (gridStreamCover k m) (arrivedPrefix (k + m * k) k) := by
  classical
  unfold coverageValue
  have hsub : range (k * k) ⊆
      ((arrivedPrefix (k + m * k) k).biUnion (gridStreamCover k m)).map Fin.valEmbedding := by
    intro y hy
    have hy' : y < k * k := mem_range.mp hy
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hy'
      · exact h
    have hr : y / k < k := (Nat.div_lt_iff_lt_mul hk).mpr hy'
    refine mem_map.mpr ⟨⟨y, by omega⟩, mem_biUnion.mpr ⟨⟨y / k, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp [arrivedPrefix, hr]
    · simp [gridStreamCover, hr, hy']
  have := card_le_card hsub
  rw [card_range, card_map] at this
  exact_mod_cast this

/-- The columns `b_{1,j}, ..., b_{k,j}` of stage `j`, at the stream positions
`j k + i` with `i < k`. -/
def stageColumns (k m j : ℕ) : Finset (Fin (k + m * k)) :=
  univ.filter fun e => j * k ≤ e.val ∧ e.val < (j + 1) * k

theorem card_stageColumns {k m j : ℕ} (hj : j ≤ m) : (stageColumns k m j).card = k := by
  have hjm : j * k ≤ m * k := Nat.mul_le_mul_right k hj
  have hsucc : (j + 1) * k = j * k + k := Nat.succ_mul j k
  have hmap : (stageColumns k m j).map Fin.valEmbedding = Ico (j * k) ((j + 1) * k) := by
    ext x
    simp only [stageColumns, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      mem_Ico]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, by omega⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, hmap, Nat.card_Ico]
  omega

theorem stageColumns_subset {k m j t : ℕ} (ht : (j + 1) * k ≤ t) :
    stageColumns k m j ⊆ arrivedPrefix (k + m * k) t := by
  intro e he
  simp only [stageColumns, arrivedPrefix, mem_filter, mem_univ, true_and] at he ⊢
  omega

/-- The columns of stage `j ≥ 1` cover the grid and `j` auxiliary elements per
column: `k² + k j` elements, the value `k (k + j)` of `B_j` in Appendix B.1. -/
theorem coverage_stage {k m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (k : ℝ) * k + k * j ≤ coverageValue (gridStreamCover k m) (stageColumns k m j) := by
  classical
  unfold coverageValue
  have hjmk : j * k ≤ m * k := Nat.mul_le_mul_right k hjm
  have hsucc : (j + 1) * k = j * k + k := Nat.succ_mul j k
  have hpred : j * k = (j - 1) * k + k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
  set T := (stageColumns k m j).biUnion (gridStreamCover k m)
  have hcore : range (k * k) ⊆ T.map Fin.valEmbedding := by
    intro y hy
    have hy' : y < k * k := mem_range.mp hy
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hy'
      · exact h
    have hyk : y % k < k := Nat.mod_lt _ hk
    refine mem_map.mpr ⟨⟨y, by omega⟩, mem_biUnion.mpr ⟨⟨j * k + y % k, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp only [stageColumns, mem_filter, mem_univ, true_and]
      omega
    · simp only [gridStreamCover, mem_filter, mem_univ, true_and]
      rw [if_neg (by omega)]
      refine Or.inl ⟨hy', ?_⟩
      rw [show j * k + y % k - k = (j - 1) * k + y % k by omega, (mul_add_div_mod hyk).2]
  have haux : ((range k ×ˢ range j).image fun p => k * k + p.1 * m + p.2) ⊆
      T.map Fin.valEmbedding := by
    intro y hy
    obtain ⟨⟨i, l⟩, hil, rfl⟩ := mem_image.mp hy
    obtain ⟨hi, hl⟩ := mem_product.mp hil
    have hi' : i < k := mem_range.mp hi
    have hl' : l < j := mem_range.mp hl
    have hlm : l < m := by omega
    have him : (i + 1) * m ≤ k * m := Nat.mul_le_mul_right m hi'
    have hisucc : (i + 1) * m = i * m + m := Nat.succ_mul i m
    refine mem_map.mpr ⟨⟨k * k + i * m + l, by omega⟩,
      mem_biUnion.mpr ⟨⟨j * k + i, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp only [stageColumns, mem_filter, mem_univ, true_and]
      omega
    · simp only [gridStreamCover, mem_filter, mem_univ, true_and]
      rw [if_neg (by omega)]
      refine Or.inr ⟨by omega, ?_, ?_⟩
      · rw [show k * k + i * m + l - k * k = i * m + l by omega,
          show j * k + i - k = (j - 1) * k + i by omega, (mul_add_div_mod hlm).1,
          (mul_add_div_mod hi').2]
      · rw [show k * k + i * m + l - k * k = i * m + l by omega,
          show j * k + i - k = (j - 1) * k + i by omega, (mul_add_div_mod hlm).2,
          (mul_add_div_mod hi').1]
        omega
  have hdisj : Disjoint (range (k * k))
      ((range k ×ˢ range j).image fun p => k * k + p.1 * m + p.2) := by
    rw [disjoint_left]
    intro a ha hb
    obtain ⟨p, -, rfl⟩ := mem_image.mp hb
    have := mem_range.mp ha
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => k * k + p.1 * m + p.2) ↑(range k ×ˢ range j) := by
    intro p hp q hq hpq
    have hp2 : p.2 < m := by
      have := (mem_product.mp (mem_coe.mp hp)).2
      have := mem_range.mp this
      omega
    have hq2 : q.2 < m := by
      have := (mem_product.mp (mem_coe.mp hq)).2
      have := mem_range.mp this
      omega
    have hpq' : p.1 * m + p.2 = q.1 * m + q.2 := by
      simp only at hpq
      omega
    have h1 := mul_add_div_mod (a := p.1) hp2
    have h2 := mul_add_div_mod (a := q.1) hq2
    rw [hpq'] at h1
    exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
  have hcard := card_le_card (union_subset hcore haux)
  rw [card_union_of_disjoint hdisj, card_range, card_image_of_injOn hinj, card_product,
    card_range, card_range, card_map] at hcard
  exact_mod_cast hcard

end ConsistentSubmodular.GridStream
