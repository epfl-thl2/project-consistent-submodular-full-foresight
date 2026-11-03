module

public import ConsistentSubmodular.Deterministic.Reduction.Thinning

@[expose] public section

/-! A finite forced set bounding all remaining singleton marginals. -/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

/-- A smallest maximizer of the penalized objective replaces the greedy
construction of the forced set `D` in Appendix B.2.3. Its removal marginals are
strictly above the penalty, and its insertion marginals are at most the
penalty. -/
theorem exists_penalized_core (U : Finset (Fin n)) (c : ℝ) :
    ∃ D ⊆ U,
      (∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) ∧
      (∀ e ∈ D, c < f.value D - f.value (D.erase e)) := by
  classical
  let score := fun D : Finset (Fin n) => f.value D - c * D.card
  obtain ⟨D₀, hD₀, hmax₀⟩ := U.powerset.exists_max_image score ⟨∅, by simp⟩
  let maximizers := U.powerset.filter (fun D => score D = score D₀)
  have hnonempty : maximizers.Nonempty := ⟨D₀, by simp [maximizers, hD₀]⟩
  obtain ⟨D, hD, hmin⟩ := maximizers.exists_min_image Finset.card hnonempty
  have hDU : D ⊆ U := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
  have hDscore : score D = score D₀ := (Finset.mem_filter.mp hD).2
  have hmax : ∀ A ⊆ U, score A ≤ score D := by
    intro A hAU
    rw [hDscore]
    exact hmax₀ A (Finset.mem_powerset.mpr hAU)
  refine ⟨D, hDU, ?_, ?_⟩
  · intro e heU heD
    have h := hmax (insert e D) (Finset.insert_subset heU hDU)
    have hc : ((insert e D).card : ℝ) = (D.card : ℝ) + 1 := by
      rw [Finset.card_insert_of_notMem heD]
      push_cast
      rfl
    dsimp [score] at h
    rw [hc] at h
    linarith
  · intro e heD
    have hsub : D.erase e ⊆ U := (Finset.erase_subset e D).trans hDU
    have hweak := hmax (D.erase e) hsub
    have hstrict : score (D.erase e) < score D := by
      apply lt_of_le_of_ne hweak
      intro heq
      have hmem : D.erase e ∈ maximizers := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hsub, heq.trans hDscore⟩
      have hcard := hmin (D.erase e) hmem
      have hlt := Finset.card_erase_lt_of_mem heD
      omega
    have hc : ((D.erase e).card : ℝ) + 1 = (D.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one heD
    dsimp [score] at hstrict
    rw [← hc] at hstrict
    nlinarith only [hstrict]

/-- Every instance admits fewer than `H` forced elements, after which every
remaining element has marginal at most `c`. The scale bound is needed only
for feasible sets of size at most `k`, and `H ≤ k`. -/
theorem exists_forced_set (U : Finset (Fin n)) (k H : ℕ) (hH : 0 < H) (hHk : H ≤ k)
    (c V : ℝ) (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (hpay : V ≤ (H : ℝ) * c) :
    ∃ D ⊆ U, D.card < H ∧
      ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c := by
  classical
  obtain ⟨D, hDU, hins, hrem⟩ := f.exists_penalized_core U c
  refine ⟨D, hDU, ?_, hins⟩
  by_contra hcard
  have hHD : H ≤ D.card := le_of_not_gt hcard
  obtain ⟨A, hAD, hAH⟩ := Finset.exists_subset_card_eq hHD
  have hAnonempty : A.Nonempty := Finset.card_pos.mp (by omega)
  have hstrict : (∑ e ∈ A, c) < ∑ e ∈ A, (f.value A - f.value (A.erase e)) := by
    exact Finset.sum_lt_sum_of_nonempty hAnonempty (fun e he =>
      (hrem e (hAD he)).trans_le (f.removal_marginal_le hAD he))
  have hsum := f.sum_removal_marginals_le A
  have hval := hscale A (hAD.trans hDU) (by omega)
  have h0 := f.nonnegative ∅
  simp only [Finset.sum_const, nsmul_eq_mul, hAH] at hstrict
  linarith

/-- Contraction by any additional buffer only decreases the remaining
singleton marginals certified by a forced set. -/
theorem forced_marginal_under_buffer (D Q : Finset (Fin n)) (e : Fin n) {c : ℝ}
    (h : f.value (insert e D) - f.value D ≤ c) :
    f.value (insert e (D ∪ Q)) - f.value (D ∪ Q) ≤ c := by
  have hdec := f.diminishing_returns (Finset.subset_union_left : D ⊆ D ∪ Q) {e}
  simp only [Finset.union_singleton] at hdec
  exact hdec.trans h

end ConsistentSubmodular.Objective
