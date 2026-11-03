module

public import ConsistentSubmodular.MainStatements

@[expose] public section

/-!
# The transition schedule of Algorithm 1

A transition of Algorithm 1 (Appendix A.3) changes the old core `C` into the
new core `A`. Following the proof of Lemma 1, the elements of `C \ A` are paired
with the elements of `A \ C`; the `r`-th operation performs the `r`-th exchange,
or the `r`-th remaining deletion or insertion. After `r` operations the core is
`path C A r`. Every intermediate core has size at most the larger endpoint
core, and each operation changes at most two elements.

A block of `ℓ` updates is cut into `h` contiguous subblocks whose lengths differ
by at most one; subblock `σ` consists of the updates `lo σ + 1, ..., hi σ` of the
block. Inside the selected subblock the operations are spread evenly, `s` per
update.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-! ### Exchanges -/

/-- The first `r` elements of `D` in a fixed enumeration. -/
def pre (D : Finset (Fin n)) (r : ℕ) : Finset (Fin n) := (D.toList.take r).toFinset

theorem pre_subset (D : Finset (Fin n)) (r : ℕ) : pre D r ⊆ D := by
  intro x hx
  exact Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hx))

theorem card_pre (D : Finset (Fin n)) (r : ℕ) : (pre D r).card = min r D.card := by
  rw [pre, List.toFinset_card_of_nodup (List.Nodup.sublist (List.take_sublist r _)
    D.nodup_toList), List.length_take, Finset.length_toList]

theorem pre_mono (D : Finset (Fin n)) {r r' : ℕ} (h : r ≤ r') : pre D r ⊆ pre D r' := by
  intro x hx
  exact List.mem_toFinset.mpr ((List.take_prefix_take_left h).subset (List.mem_toFinset.mp hx))

@[simp] theorem pre_zero (D : Finset (Fin n)) : pre D 0 = ∅ := by
  simp [pre]

theorem pre_of_card_le (D : Finset (Fin n)) {r : ℕ} (h : D.card ≤ r) : pre D r = D := by
  rw [pre, List.take_of_length_le (by rw [Finset.length_toList]; exact h),
    Finset.toList_toFinset]

/-- The core after `r` operations of the transition from `C` to `A`: the first
`r` elements of `C \ A` are deleted and the first `r` elements of `A \ C` are
inserted. -/
def path (C A : Finset (Fin n)) (r : ℕ) : Finset (Fin n) :=
  (C \ pre (C \ A) r) ∪ pre (A \ C) r

/-- The number of operations of the transition, `max(|C \ A|, |A \ C|)`. -/
def operations (C A : Finset (Fin n)) : ℕ := max (C \ A).card (A \ C).card

@[simp] theorem path_zero (C A : Finset (Fin n)) : path C A 0 = C := by
  simp [path]

theorem path_of_operations_le (C A : Finset (Fin n)) {r : ℕ} (h : operations C A ≤ r) :
    path C A r = A := by
  have h1 : (C \ A).card ≤ r := le_trans (le_max_left _ _) h
  have h2 : (A \ C).card ≤ r := le_trans (le_max_right _ _) h
  rw [path, pre_of_card_le _ h1, pre_of_card_le _ h2]
  ext x
  simp only [Finset.mem_union, Finset.mem_sdiff]
  tauto

theorem path_subset (C A : Finset (Fin n)) (r : ℕ) : path C A r ⊆ C ∪ A := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mp (pre_subset _ _ hx)).1

/-- Every intermediate core has size at most the larger endpoint core. -/
theorem card_path_le (C A : Finset (Fin n)) (r : ℕ) :
    (path C A r).card ≤ max C.card A.card := by
  have hu := Finset.card_union_le (C \ pre (C \ A) r) (pre (A \ C) r)
  have hs : (C \ pre (C \ A) r).card = C.card - (pre (C \ A) r).card :=
    Finset.card_sdiff_of_subset ((pre_subset _ _).trans Finset.sdiff_subset)
  have h1 := card_pre (C \ A) r
  have h2 := card_pre (A \ C) r
  have h3 := Finset.card_sdiff_add_card_inter C A
  have h4 := Finset.card_sdiff_add_card_inter A C
  have h5 : (C ∩ A).card = (A ∩ C).card := by rw [Finset.inter_comm]
  have h6 : (pre (C \ A) r).card ≤ C.card :=
    Finset.card_le_card ((pre_subset _ _).trans Finset.sdiff_subset)
  rw [path]
  omega

/-- Operations `r + 1, ..., r'` change at most two elements each. -/
theorem recourse_path_le (C A : Finset (Fin n)) {r r' : ℕ} (h : r ≤ r') :
    recourse (path C A r') (path C A r) ≤ 2 * (r' - r) := by
  have hP := pre_mono (C \ A) h
  have hQ := pre_mono (A \ C) h
  have hsub : (path C A r' \ path C A r) ∪ (path C A r \ path C A r') ⊆
      (pre (A \ C) r' \ pre (A \ C) r) ∪ (pre (C \ A) r' \ pre (C \ A) r) := by
    intro x hx
    simp only [path, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
    have hP' := @hP x
    have hQ' := @hQ x
    tauto
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hQ, Finset.card_sdiff_of_subset hP, card_pre, card_pre,
    card_pre, card_pre] at hc
  unfold recourse
  omega

/-- The recourse between two unions is at most the sum of the recourses. -/
theorem recourse_union_le (X Y X' Y' : Finset (Fin n)) :
    recourse (X ∪ Y) (X' ∪ Y') ≤ recourse X X' + recourse Y Y' := by
  unfold recourse
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_union, Finset.mem_sdiff] at hx ⊢
  tauto

/-- One new arrival changes the arrived part of a block by at most one element. -/
theorem recourse_arrival_le (B : Finset (Fin n)) (t : ℕ) :
    recourse (B ∩ arrivedPrefix n (t + 1)) (B ∩ arrivedPrefix n t) ≤ 1 := by
  unfold recourse
  have hsub : ((B ∩ arrivedPrefix n (t + 1)) \ (B ∩ arrivedPrefix n t)) ∪
      ((B ∩ arrivedPrefix n t) \ (B ∩ arrivedPrefix n (t + 1))) ⊆
      Finset.univ.filter (fun e : Fin n => e.val = t) := by
    intro x hx
    simp only [arrivedPrefix, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨⟨hb, h1⟩, h2⟩ | ⟨⟨hb, h1⟩, h2⟩
    · have h3 : ¬ x.val < t := fun h => h2 ⟨hb, h⟩
      omega
    · exact absurd ⟨hb, by omega⟩ h2
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact Fin.ext (ha.trans hb.symm)

/-! ### Subblocks -/

/-- Subblock `σ` of a block of `ℓ` updates consists of the updates
`lo σ + 1, ..., hi σ`. -/
def lo (ℓ h σ : ℕ) : ℕ := σ * ℓ / h

/-- The last update of subblock `σ`. -/
def hi (ℓ h σ : ℕ) : ℕ := (σ + 1) * ℓ / h

/-- The number of updates of subblock `σ` among the first `r` updates of the
block. -/
def elapsed (ℓ h σ r : ℕ) : ℕ := min (hi ℓ h σ) r - lo ℓ h σ

/-- Each subblock has at least `⌊ℓ/h⌋` updates. -/
theorem div_le_hi_sub_lo (ℓ h σ : ℕ) : ℓ / h ≤ hi ℓ h σ - lo ℓ h σ := by
  have h1 := Nat.add_div_le_add_div (σ * ℓ) ℓ h
  have h2 : (σ + 1) * ℓ = σ * ℓ + ℓ := by ring
  unfold hi lo
  rw [h2]
  omega

theorem hi_le (ℓ h : ℕ) {σ : ℕ} (hσ : σ < h) : hi ℓ h σ ≤ ℓ := by
  rcases Nat.eq_zero_or_pos h with hh | hh
  · omega
  calc (σ + 1) * ℓ / h ≤ h * ℓ / h := Nat.div_le_div_right (Nat.mul_le_mul_right ℓ hσ)
    _ = ℓ := Nat.mul_div_cancel_left ℓ hh

/-- Subblocks are disjoint and ordered. -/
theorem hi_le_lo (ℓ h : ℕ) {σ σ' : ℕ} (hσ : σ < σ') : hi ℓ h σ ≤ lo ℓ h σ' :=
  Nat.div_le_div_right (Nat.mul_le_mul_right ℓ hσ)

theorem elapsed_of_le_lo {ℓ h σ r : ℕ} (hr : r ≤ lo ℓ h σ) : elapsed ℓ h σ r = 0 := by
  unfold elapsed
  omega

theorem elapsed_of_hi_le {ℓ h σ r : ℕ} (hr : hi ℓ h σ ≤ r) :
    elapsed ℓ h σ r = hi ℓ h σ - lo ℓ h σ := by
  unfold elapsed
  rw [min_eq_left hr]

theorem elapsed_succ_le (ℓ h σ r : ℕ) : elapsed ℓ h σ (r + 1) ≤ elapsed ℓ h σ r + 1 := by
  unfold elapsed
  omega

theorem elapsed_mono (ℓ h σ : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    elapsed ℓ h σ r ≤ elapsed ℓ h σ r' := by
  unfold elapsed
  omega

/-- At most one subblock contains a given update strictly inside its range. -/
theorem card_inside_le_one (ℓ h r : ℕ) :
    (Finset.univ.filter (fun σ : Fin h => lo ℓ h σ < r ∧ r < hi ℓ h σ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_contra hab
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
  · have := hi_le_lo ℓ h hlt
    omega
  · have := hi_le_lo ℓ h hlt
    omega

/-- The number of operations performed after `r` updates of a block whose
selected subblock is `σ`, with `s` operations per update and `R` operations
in total. -/
def done (ℓ h s R σ r : ℕ) : ℕ := min R (s * elapsed ℓ h σ r)

theorem done_of_le_lo {ℓ h s R σ r : ℕ} (hr : r ≤ lo ℓ h σ) : done ℓ h s R σ r = 0 := by
  simp [done, elapsed_of_le_lo hr]

theorem done_of_hi_le {ℓ h s R σ r : ℕ} (hr : hi ℓ h σ ≤ r)
    (hR : R ≤ s * (hi ℓ h σ - lo ℓ h σ)) : done ℓ h s R σ r = R := by
  rw [done, elapsed_of_hi_le hr]
  exact min_eq_left hR

theorem done_mono (ℓ h s R σ : ℕ) {r r' : ℕ} (hr : r ≤ r') :
    done ℓ h s R σ r ≤ done ℓ h s R σ r' :=
  min_le_min_left R (Nat.mul_le_mul_left s (elapsed_mono ℓ h σ hr))

theorem done_succ_le (ℓ h s R σ r : ℕ) :
    done ℓ h s R σ (r + 1) ≤ done ℓ h s R σ r + s := by
  have he := elapsed_succ_le ℓ h σ r
  have hm : s * elapsed ℓ h σ (r + 1) ≤ s * elapsed ℓ h σ r + s := by
    calc s * elapsed ℓ h σ (r + 1) ≤ s * (elapsed ℓ h σ r + 1) := Nat.mul_le_mul_left s he
      _ = s * elapsed ℓ h σ r + s := by ring
  unfold done
  omega

end ConsistentSubmodular.Checkpoints
