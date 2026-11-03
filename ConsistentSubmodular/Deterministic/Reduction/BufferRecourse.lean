module

public import ConsistentSubmodular.Deterministic.Reduction.SchedulingBasics

@[expose] public section

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_sdiff_le (A B R T : Finset (Fin n)) :
    recourse (A \ R) (B \ T) ≤ recourse A B + recourse R T := by
  have hsub : ((A \ R) \ (B \ T)) ∪ ((B \ T) \ (A \ R)) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((R \ T) ∪ (T \ R)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem prefix_recourse_le {s t : ℕ} (hst : s ≤ t) :
    recourse (arrivedPrefix n t) (arrivedPrefix n s) ≤ t - s := by
  have hsub : arrivedPrefix n s ⊆ arrivedPrefix n t := arrivedPrefix_mono hst
  have he : arrivedPrefix n s \ arrivedPrefix n t = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr hsub
  simpa [recourse, he] using (prefix_difference_card_le (n := n) s t)

theorem rollingBuffer_recourse_le (width t : ℕ) :
    recourse (rollingBuffer n width (t + 1)) (rollingBuffer n width t) ≤ 2 := by
  have hnew := prefix_recourse_le (n := n) (show t ≤ t + 1 by omega)
  have hold := prefix_recourse_le (n := n) (show t - width ≤ t + 1 - width by omega)
  have hh := recourse_sdiff_le (arrivedPrefix n (t + 1)) (arrivedPrefix n t)
    (arrivedPrefix n (t + 1 - width)) (arrivedPrefix n (t - width))
  change recourse (rollingBuffer n width (t + 1)) (rollingBuffer n width t) ≤ _ at hh
  omega

theorem rollingBuffer_subset (width t : ℕ) : rollingBuffer n width t ⊆ arrivedPrefix n t :=
  Finset.sdiff_subset

@[simp] theorem rollingBuffer_zero (width : ℕ) : rollingBuffer n width 0 = ∅ := by
  simp [rollingBuffer, arrivedPrefix]

end ConsistentSubmodular
