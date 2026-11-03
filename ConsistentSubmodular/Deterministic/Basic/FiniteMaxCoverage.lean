module

public import ConsistentSubmodular.Deterministic.Basic.CompatibleProfiles

@[expose] public section

/-! Finite weighted coverage realization of a nonnegative maximum function. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

/-- A finite nested coverage realization. The upward property ensures that
every maximum-weight label covers each atom; zero-weight labels cover none. -/
structure MaximumCoverage {d : ℕ} (w : Fin d → ℝ) where
  atomCount : ℕ
  labels : Fin atomCount → Finset (Fin d)
  weight : Fin atomCount → ℝ
  weight_positive : ∀ a, 0 < weight a
  labels_nonempty : ∀ a, (labels a).Nonempty
  labels_positive : ∀ a i, i ∈ labels a → 0 < w i
  labels_upward : ∀ a i j, w i ≤ w j → i ∈ labels a → j ∈ labels a
  value_eq : ∀ I : Finset (Fin d), finiteMaximum I w =
    ∑ a, if (labels a ∩ I).Nonempty then weight a else 0

theorem maximum_split {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ i, 0 < w i → c ≤ w i)
    (I : Finset (Fin d)) :
    finiteMaximum I w =
      (if ((Finset.univ.filter (fun i => 0 < w i)) ∩ I).Nonempty then c else 0) +
        finiteMaximum I (fun i => if 0 < w i then w i - c else 0) := by
  classical
  let w' := fun i => if 0 < w i then w i - c else 0
  have hw' : ∀ i, 0 ≤ w' i := by
    intro i
    dsimp [w']
    split_ifs with hi
    · exact sub_nonneg.mpr (hmin i hi)
    · rfl
  have hmax' := finiteMaximum_nonnegative (I := I) (fun i _ => hw' i)
  by_cases hpos : ((Finset.univ.filter (fun i => 0 < w i)) ∩ I).Nonempty
  · rw [if_pos hpos]
    obtain ⟨i, hi⟩ := hpos
    have hiw : 0 < w i := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
    have hiI := (Finset.mem_inter.mp hi).2
    have hcmax : c ≤ finiteMaximum I w := (hmin i hiw).trans (le_finiteMaximum hiI)
    have hu : finiteMaximum I w ≤ c + finiteMaximum I w' := by
      apply finiteMaximum_le (add_nonneg hc.le hmax')
      intro j hj
      by_cases hjw : 0 < w j
      · have hle : w' j ≤ finiteMaximum I w' := le_finiteMaximum hj
        simp only [w', if_pos hjw] at hle
        linarith
      · have hwj : w j = 0 := le_antisymm (le_of_not_gt hjw) (hw j)
        rw [hwj]
        exact add_nonneg hc.le hmax'
    have hl : finiteMaximum I w' ≤ finiteMaximum I w - c := by
      apply finiteMaximum_le (sub_nonneg.mpr hcmax)
      intro j hj
      by_cases hjw : 0 < w j
      · simpa only [w', if_pos hjw] using sub_le_sub_right (le_finiteMaximum (g := w) hj) c
      · simpa only [w', if_neg hjw] using sub_nonneg.mpr hcmax
    change finiteMaximum I w = c + finiteMaximum I w'
    linarith
  · rw [if_neg hpos, zero_add]
    have hz : ∀ i ∈ I, w i = 0 := by
      intro i hi
      have hnot : ¬0 < w i := by
        intro hwi
        exact hpos ⟨i, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwi⟩, hi⟩⟩
      exact le_antisymm (le_of_not_gt hnot) (hw i)
    have hzero : finiteMaximum I w = 0 := le_antisymm
      (finiteMaximum_le le_rfl (fun i hi => (hz i hi).le))
      (finiteMaximum_nonnegative (fun i _ => hw i))
    have hzero' : finiteMaximum I w' = 0 := le_antisymm
      (finiteMaximum_le le_rfl (fun i hi => by simp [w', hz i hi]))
      hmax'
    exact hzero.trans hzero'.symm

theorem exists_maximumCoverage {d : ℕ} (w : Fin d → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Nonempty (MaximumCoverage w) := by
  classical
  induction hs : (Finset.univ.filter (fun i => 0 < w i)).card
      using Nat.strong_induction_on generalizing w with
  | h s ih =>
    let active := Finset.univ.filter (fun i => 0 < w i)
    by_cases hempty : active = ∅
    · refine ⟨{
        atomCount := 0
        labels := Fin.elim0
        weight := Fin.elim0
        weight_positive := fun a => Fin.elim0 a
        labels_nonempty := fun a => Fin.elim0 a
        labels_positive := fun a => Fin.elim0 a
        labels_upward := fun a => Fin.elim0 a
        value_eq := ?_
      }⟩
      intro I
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      apply le_antisymm
      · apply finiteMaximum_le le_rfl
        intro i _
        have hnot : ¬0 < w i := by
          intro hi
          have himem : i ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
          rw [hempty] at himem
          exact Finset.notMem_empty i himem
        exact le_of_not_gt hnot
      · exact finiteMaximum_nonnegative (fun i _ => hw i)
    · have hactive : active.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨a, ha, hamin⟩ := active.exists_min_image w hactive
      have hapos : 0 < w a := (Finset.mem_filter.mp ha).2
      have hmin : ∀ i, 0 < w i → w a ≤ w i := by
        intro i hi
        exact hamin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      let w' := fun i => if 0 < w i then w i - w a else 0
      have hw' : ∀ i, 0 ≤ w' i := by
        intro i
        dsimp [w']
        split_ifs with hi
        · exact sub_nonneg.mpr (hmin i hi)
        · rfl
      have hsupport : Finset.univ.filter (fun i => 0 < w' i) ⊆ active.erase a := by
        intro i hi
        have hiw' : 0 < w' i := (Finset.mem_filter.mp hi).2
        have hiw : 0 < w i := by
          by_contra hnot
          simp [w', hnot] at hiw'
        have hia : i ≠ a := by
          intro heq
          subst i
          simp [w', hapos] at hiw'
        exact Finset.mem_erase.mpr ⟨hia, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiw⟩⟩
      have hsmall : (Finset.univ.filter (fun i => 0 < w' i)).card < s := by
        have hle := Finset.card_le_card hsupport
        have hlt : (active.erase a).card < active.card := Finset.card_erase_lt_of_mem ha
        change active.card = s at hs
        omega
      obtain ⟨R⟩ := ih _ hsmall w' hw' rfl
      refine ⟨{
        atomCount := R.atomCount + 1
        labels := Fin.cases active R.labels
        weight := Fin.cases (w a) R.weight
        weight_positive := ?_
        labels_nonempty := ?_
        labels_positive := ?_
        labels_upward := ?_
        value_eq := ?_
      }⟩
      · intro b
        exact Fin.cases hapos R.weight_positive b
      · intro b
        exact Fin.cases hactive R.labels_nonempty b
      · intro b
        refine Fin.cases ?_ ?_ b
        · intro i hi
          exact (Finset.mem_filter.mp hi).2
        · intro b i hi
          have hp := R.labels_positive b i hi
          by_contra hnot
          simp [w', hnot] at hp
      · intro b
        refine Fin.cases ?_ ?_ b
        · intro i j hij hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hij⟩
        · intro b i j hij hi
          have hip := R.labels_positive b i hi
          have hiw : 0 < w i := by
            by_contra hnot
            simp [w', hnot] at hip
          have hjw : 0 < w j := lt_of_lt_of_le hiw hij
          exact R.labels_upward b i j (by simpa only [w', if_pos hiw, if_pos hjw] using sub_le_sub_right hij (w a)) hi
      · intro I
        rw [Fin.sum_univ_succ]
        simp only [Fin.cases_zero, Fin.cases_succ]
        rw [← R.value_eq]
        exact maximum_split w hw (w a) hapos hmin I

end ConsistentSubmodular
