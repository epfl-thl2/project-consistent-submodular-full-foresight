module

public import ConsistentSubmodular.Deterministic.Reduction.BlockSchedule
public import ConsistentSubmodular.Deterministic.Reduction.BufferRecourse

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

/-- Local rounded objects supply all the data needed by the protected clock.
The conditions include every intermediate physical operation. -/
structure ProtectedPrograms {n b ell : ℕ} (f : Objective n) (κ : ℕ) (β : ℝ)
    {F : ℕ → ℝ} {η : ℝ} (C : ProtectedClock F η b ell) (R B : ℕ) where
  path : ℕ → SetOperationPath n
  initial : (path 0).node 0 = ∅
  joins : ∀ i, (path i).node (path i).length = (path (i + 1)).node 0
  length : ∀ i, (path i).length ≤ R * ell
  cardinality : ∀ i j, ((path i).node j).card ≤ B
  arrived : ∀ i j, (path i).node j ⊆ arrivedPrefix n (C.start i)
  transition : ∀ i j, β * f.prefixOptimum κ (C.start (i + 1)) ≤
    f.value ((path (i + 1)).node j ∪
      (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)))
  checkpoint : ∀ i t, C.start i ≤ t → t ≤ C.start (i + 1) →
    β * f.prefixOptimum κ t ≤ f.value ((path i).node (path i).length ∪
      (arrivedPrefix n t \ arrivedPrefix n (C.start i)))

namespace ProtectedPrograms

variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}
variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

def core (t : ℕ) : Finset (Fin n) :=
  (C.coreBlocks P.path P.initial P.joins P.length).trajectory t

def selected (t : ℕ) : Finset (Fin n) := P.core t ∪ rollingBuffer n (4 * b) t

@[simp] theorem core_zero : P.core 0 = ∅ := C.coreBlocks_initial _ _ _ _

@[simp] theorem selected_zero : P.selected 0 = ∅ := by simp [selected]

theorem recourse_bound (hb : 0 < b) (t : ℕ) :
    recourse (P.selected (t + 1)) (P.selected t) ≤ R + 2 := by
  have hc := C.coreBlocks_recourse (R := R) hb P.path P.initial P.joins P.length t
  have hbuf := rollingBuffer_recourse_le (n := n) (4 * b) t
  have hh := recourse_union_le (P.core (t + 1)) (P.core t)
    (rollingBuffer n (4 * b) (t + 1)) (rollingBuffer n (4 * b) t)
  exact hh.trans (Nat.add_le_add hc hbuf)

theorem core_in_block (i t : ℕ) (ht : t / b = i + 1) :
    P.core t = (P.path i).node (R * (t - C.start i)) :=
  C.coreBlocks_in_block _ _ _ _ i t ht

theorem core_cardinality (t : ℕ) : (P.core t).card ≤ B := by
  cases h : t / b with
  | zero => rw [core, C.coreBlocks_before_first _ _ _ _ t h]; simp
  | succ i => rw [P.core_in_block i t h]; exact P.cardinality _ _

theorem cardinality_bound (t : ℕ) : (P.selected t).card ≤ B + 4 * b :=
  (Finset.card_union_le _ _).trans (Nat.add_le_add (P.core_cardinality t)
    (rollingBuffer_card_le _ _))

theorem arrived_bound (t : ℕ) : P.selected t ⊆ arrivedPrefix n t := by
  apply Finset.union_subset
  · cases hdiv : t / b with
    | zero => rw [core, C.coreBlocks_before_first _ _ _ _ t hdiv]; exact Finset.empty_subset _
    | succ i =>
      rw [P.core_in_block i t hdiv]
      by_cases ht : C.start i ≤ t
      · exact (P.arrived _ _).trans (arrivedPrefix_mono ht)
      · have he : t - C.start i = 0 := by omega
        rw [he, Nat.mul_zero]
        cases i with
        | zero => rw [P.initial]; exact Finset.empty_subset _
        | succ i =>
          rw [← P.joins i]
          have hu := C.upper i
          have hbnd := Nat.div_mul_le_self t b
          rw [hdiv] at hbnd
          have ha : C.start i ≤ t := (Nat.le_add_right _ _).trans
            (hu.trans (by simpa only [Nat.add_assoc] using hbnd))
          exact (P.arrived _ _).trans (arrivedPrefix_mono ha)
  · exact rollingBuffer_subset _ _

end ProtectedPrograms

namespace ProtectedPrograms

variable {n b ell κ k R B : ℕ} {f : Objective n} {β η γ : ℝ}
variable {C : ProtectedClock (f.prefixOptimum k) η b ell}
variable (P : ProtectedPrograms f κ β C R B)

/-- The local certificates imply the approximation at every actual time,
including unfinished transitions and both sides of block boundaries. -/
theorem value_bound (hb : 0 < b) (hη : 0 ≤ η) (hγ : γ ≤ (3 : ℝ) / 4)
    (compare : ∀ s t, f.prefixOptimum k t ≤ (1 + η) * f.prefixOptimum k s →
      γ * f.prefixOptimum k t ≤ β * f.prefixOptimum κ s) (t : ℕ) :
    γ * f.prefixOptimum k t ≤ f.value (P.selected t) := by
  have hself (s : ℕ) : γ * f.prefixOptimum k s ≤ β * f.prefixOptimum κ s := by
    apply compare s s
    have hh := mul_nonneg hη (f.prefixOptimum_nonnegative k s)
    nlinarith
  have hbuffer : rollingBuffer n (4 * b) t ⊆ P.selected t := Finset.subset_union_right
  have hfull (ht : t ≤ C.start 0 + ell) :
      γ * f.prefixOptimum k t ≤ f.value (P.selected t) := by
    have hp : f.prefixOptimum k t ≤ f.value (arrivedPrefix n t) := by
      have hh := f.monotone _ _ (f.bufferedOptimizer_spec (arrivedPrefix n t) ∅ k).1
      simpa [Objective.prefixOptimum, Objective.bufferedOptimum] using hh
    have hm := f.monotone _ _ (show arrivedPrefix n t ⊆ P.selected t by
      rw [← C.initial_buffer_full t ht]; exact hbuffer)
    have hc := mul_nonneg (show 0 ≤ 1 - γ by linarith) (f.prefixOptimum_nonnegative k t)
    nlinarith
  by_cases hinitial : t ≤ C.start 0 + ell
  · exact hfull hinitial
  have hr := Nat.mod_lt t hb
  have hd := Nat.mod_add_div t b
  cases hdiv : t / b with
  | zero =>
    rw [hdiv] at hd
    have hl := C.lower 0
    exact hfull (by simp only [zero_add, one_mul] at hl; omega)
  | succ i =>
    have hcore := P.core_in_block i t hdiv
    rw [hdiv] at hd
    have hlo : (i + 1) * b ≤ t := by simpa only [hdiv] using Nat.div_mul_le_self t b
    have hhi : t < (i + 2) * b := by
      simpa only [hdiv, Nat.add_assoc, Nat.mul_comm] using Nat.lt_mul_div_succ t hb
    by_cases hbefore : t < C.start i
    · have hz : R * (t - C.start i) = 0 := by simp [Nat.sub_eq_zero_of_le hbefore.le]
      rw [hz] at hcore
      cases i with
      | zero => omega
      | succ i =>
        rw [← P.joins i] at hcore
        have hu := C.upper i
        have hprev : C.start i ≤ t := by nlinarith
        have hval := P.checkpoint i t hprev hbefore.le
        have hsub := C.current_buffer_protected (n := n) i t hprev (by omega)
        have hm := f.monotone _ _ (show
            (P.path i).node (P.path i).length ∪
              (arrivedPrefix n t \ arrivedPrefix n (C.start i)) ⊆ P.selected t by
          rw [selected, hcore]
          exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
        exact (hself t).trans (hval.trans hm)
    · have hstart : C.start i ≤ t := le_of_not_gt hbefore
      by_cases hfinish : C.start i + ell ≤ t
      · have hlen : (P.path i).length ≤ R * (t - C.start i) :=
          (P.length i).trans (Nat.mul_le_mul_left R (by omega))
        rw [(P.path i).stationary _ hlen] at hcore
        have hnext : t ≤ C.start (i + 1) := by
          have hh := C.lower (i + 1)
          nlinarith
        have hval := P.checkpoint i t hstart hnext
        have hsub := C.current_buffer_protected (n := n) i t hstart (by omega)
        have hm := f.monotone _ _ (show
            (P.path i).node (P.path i).length ∪
              (arrivedPrefix n t \ arrivedPrefix n (C.start i)) ⊆ P.selected t by
          rw [selected, hcore]
          exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
        exact (hself t).trans (hval.trans hm)
      · have hend : t ≤ C.start i + ell := by omega
        rcases C.protection i with hstable | hunstable
        · have hct := compare (C.start i) t
            ((f.prefixOptimum_monotone k hend).trans hstable)
          cases i with
          | zero => omega
          | succ i =>
            have hval := P.transition i (R * (t - C.start (i + 1)))
            have hsub := C.previous_buffer_protected (n := n) i t hstart hend
            have hm := f.monotone _ _ (show
                (P.path (i + 1)).node (R * (t - C.start (i + 1))) ∪
                  (arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i)) ⊆
                  P.selected t by
              rw [selected, hcore]
              exact Finset.union_subset_union (Finset.Subset.refl _) hsub)
            exact hct.trans (hval.trans hm)
        · have hv := f.unstable_transition_buffer k C i t hstart hend hunstable
          have hm := f.monotone _ _ hbuffer
          have hc := mul_nonneg (sub_nonneg.mpr hγ) (f.prefixOptimum_nonnegative k t)
          nlinarith

end ProtectedPrograms
end ConsistentSubmodular
