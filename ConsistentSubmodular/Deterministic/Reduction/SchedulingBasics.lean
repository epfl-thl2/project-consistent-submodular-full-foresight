module

public import ConsistentSubmodular.Deterministic.Basic.Model

@[expose] public section

/-! Discrete buffer and recourse facts for protected scheduling. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_triangle (A B C : Finset (Fin n)) :
    recourse A C ≤ recourse A B + recourse B C := by
  have hsub : (A \ C) ∪ (C \ A) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((B \ C) ∪ (C \ B)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Overlap between a physical core and a buffer does not increase recourse. -/
theorem recourse_union_le (A B R T : Finset (Fin n)) :
    recourse (A ∪ R) (B ∪ T) ≤ recourse A B + recourse R T := by
  have hsub : ((A ∪ R) \ (B ∪ T)) ∪ ((B ∪ T) \ (A ∪ R)) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((R \ T) ∪ (T \ R)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

@[simp] theorem mem_arrivedPrefix (e : Fin n) (t : ℕ) :
    e ∈ arrivedPrefix n t ↔ e.val < t := by simp [arrivedPrefix]

/-- The rolling buffer contains at most one element per arrival time. -/
theorem prefix_difference_card_le (s t : ℕ) :
    (arrivedPrefix n t \ arrivedPrefix n s).card ≤ t - s := by
  have hle : (arrivedPrefix n t \ arrivedPrefix n s).card ≤
      (Finset.range (t - s)).card := by
    refine Finset.card_le_card_of_injOn (fun e : Fin n => e.val - s) ?_ ?_
    · intro e he
      change e ∈ arrivedPrefix n t \ arrivedPrefix n s at he
      change e.val - s ∈ Finset.range (t - s)
      simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he
      simp only [Finset.mem_range]
      omega
    · intro e he e' he' heq
      change e ∈ arrivedPrefix n t \ arrivedPrefix n s at he
      change e' ∈ arrivedPrefix n t \ arrivedPrefix n s at he'
      simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he he'
      change e.val - s = e'.val - s at heq
      apply Fin.ext
      omega
  simpa using hle

def rollingBuffer (n width t : ℕ) : Finset (Fin n) :=
  arrivedPrefix n t \ arrivedPrefix n (t - width)

theorem rollingBuffer_card_le (width t : ℕ) :
    (rollingBuffer n width t).card ≤ width := by
  exact (prefix_difference_card_le (t - width) t).trans (by omega)

theorem protected_buffer_subset {s t width : ℕ} (hst : s ≤ t)
    (hage : t - s ≤ width) :
    arrivedPrefix n t \ arrivedPrefix n s ⊆ rollingBuffer n width t := by
  intro e he
  simp only [Finset.mem_sdiff, mem_arrivedPrefix] at he
  simp only [rollingBuffer, Finset.mem_sdiff, mem_arrivedPrefix]
  omega

namespace Objective

variable (f : Objective n)

theorem bufferedOptimum_mono_ground {N M Q : Finset (Fin n)} {k : ℕ}
    (hNM : N ⊆ M) : f.bufferedOptimum N Q k ≤ f.bufferedOptimum M Q k := by
  have hA := f.bufferedOptimizer_spec N Q k
  exact f.le_bufferedOptimum (hA.1.trans hNM) hA.2.1

/-- Every competitor's new part is already in the window buffer. -/
theorem value_le_windowOptimum {N E A : Finset (Fin n)} {k : ℕ}
    (hAE : A ⊆ E) (hAk : A.card ≤ k) :
    f.value A ≤ f.bufferedOptimum N (E \ N) k := by
  have hsub : A ⊆ (E \ N) ∪ (A ∩ N) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases heN : e ∈ N
    · exact Or.inr ⟨he, heN⟩
    · exact Or.inl ⟨hAE he, heN⟩
  exact (f.monotone A _ hsub).trans
    (f.le_bufferedOptimum Finset.inter_subset_right
      ((Finset.card_le_card Finset.inter_subset_left).trans hAk))

theorem optimum_le_windowOptimum (N E : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum E ∅ k ≤ f.bufferedOptimum N (E \ N) k := by
  have hA := f.bufferedOptimizer_spec E ∅ k
  simpa [bufferedOptimum] using f.value_le_windowOptimum hA.1 hA.2.1

/-- The new arrivals cover the gain in the optimum. -/
theorem new_buffer_value_ge_gain (N E : Finset (Fin n)) (k : ℕ) :
    f.bufferedOptimum E ∅ k - f.bufferedOptimum N ∅ k ≤ f.value (E \ N) := by
  have hwin := f.optimum_le_windowOptimum N E k
  have hu := f.bufferedOptimum_le N (E \ N) k
  have h0 := f.nonnegative ∅
  linarith

/-- An interval whose optimum has grown by a factor of four is protected
entirely by the new arrivals. This includes zero initial optimum. -/
theorem unstable_buffer_protection (N E : Finset (Fin n)) (k : ℕ)
    (hgrowth : 4 * f.bufferedOptimum N ∅ k ≤ f.bufferedOptimum E ∅ k) :
    (3 : ℝ) / 4 * f.bufferedOptimum E ∅ k ≤ f.value (E \ N) := by
  have h := f.new_buffer_value_ge_gain N E k
  linarith

end Objective

end ConsistentSubmodular
