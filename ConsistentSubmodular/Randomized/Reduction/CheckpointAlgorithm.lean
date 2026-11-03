module

public import ConsistentSubmodular.Randomized.Reduction.CheckpointSchedule
public import ConsistentSubmodular.Randomized.Reduction.CheckpointWindow

@[expose] public section

/-!
# Algorithm 1

The trajectory of Algorithm 1 (Appendix A.3) for given checkpoint samples and
subblock choices. The stream is cut into blocks of `ℓ` arrivals. During block
`i` (the block `B_{i+1}` of the paper), the algorithm holds the old core
`A_{i-1} ∪ B_i`, changes it into the new core `A_i` inside the selected subblock
`σ_i`, and always retains the arrivals of the current block. The first block
is retained completely. This file proves that the trajectory is feasible, with
recourse `2s + 1` per update, and bounds its value outside the selected
subblock.
-/

noncomputable section
open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- The parameters of Algorithm 1: the block length `ℓ = ⌊γk⌋`, the core budget
`κ = k - 2ℓ`, the number `h = ⌈1/γ⌉` of subblocks per block, and the number `s`
of transition operations per update. -/
structure Params where
  ℓ : ℕ
  κ : ℕ
  h : ℕ
  s : ℕ

/-- The conditions on the parameters that the analysis uses for the budget `k`:
both cores and the current block fit into the budget, and `s` operations per
update finish every transition inside the shortest subblock, which has
`⌊ℓ/h⌋` updates. -/
structure Params.Valid (P : Params) (k : ℕ) : Prop where
  block_pos : 0 < P.ℓ
  subblocks_pos : 0 < P.h
  budget : P.κ + 2 * P.ℓ ≤ k
  complete : k ≤ P.s * (P.ℓ / P.h)

/-- Block `i`, the block `B_{i+1}` of the paper: the arrivals
`x_{iℓ+1}, ..., x_{(i+1)ℓ}`. -/
def block (n ℓ i : ℕ) : Finset (Fin n) := future n (i * ℓ) ℓ

/-- The old core of block `i`: `A_{i-1} ∪ B_i` in the paper's notation, and
`∅` for the first block, whose arrivals are all retained. -/
def oldCore (n ℓ : ℕ) (A : ℕ → Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  if i = 0 then ∅ else A (i - 1) ∪ block n ℓ (i - 1)

/-- The maintained set after `r` updates of block `i`: the core after the
transition operations performed so far, together with the arrivals of the
current block. -/
def state (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) (i r : ℕ) : Finset (Fin n) :=
  path (oldCore n P.ℓ A i) (A i)
      (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r) ∪
    (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r))

/-- The block `⌊(t - 1)/ℓ⌋` of the update at time `t ≥ 1`. -/
def phase (ℓ t : ℕ) : ℕ := (t - 1) / ℓ

/-- The position of time `t` inside its block, between `1` and `ℓ` for `t ≥ 1`. -/
def pos (ℓ t : ℕ) : ℕ := t - phase ℓ t * ℓ

/-- The set `ALG_t` maintained by Algorithm 1. -/
def run (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) (t : ℕ) : Finset (Fin n) :=
  state P A σ (phase P.ℓ t) (pos P.ℓ t)

/-- Random choices with positive probability: the subblock indices are in
range, and the sample of the checkpoint after block `i` is a set of at most `κ`
elements arrived by then. -/
def Good (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) : Prop :=
  ∀ i, σ i < P.h ∧ A i ⊆ arrivedPrefix n (i * P.ℓ) ∧ (A i).card ≤ P.κ

/-! ### Arrivals -/

theorem arrivedPrefix_mono {a b : ℕ} (h : a ≤ b) : arrivedPrefix n a ⊆ arrivedPrefix n b := by
  intro e he
  simp only [arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  omega

theorem future_subset (c j : ℕ) : future n c j ⊆ arrivedPrefix n (c + j) := by
  intro e he
  simp only [future, arrivedPrefix, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  omega

theorem card_future_le (c j : ℕ) : (future n c j).card ≤ j := by
  have hsub : (future n c j).map Fin.valEmbedding ⊆ Finset.Ico c (c + j) := by
    intro x hx
    simp only [Finset.mem_map, future, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact Finset.mem_Ico.mpr he
  have h := Finset.card_le_card hsub
  simpa using h

theorem block_inter (ℓ i r : ℕ) (hr : r ≤ ℓ) :
    block n ℓ i ∩ arrivedPrefix n (i * ℓ + r) = future n (i * ℓ) r := by
  ext e
  simp only [block, future, arrivedPrefix, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  omega

theorem block_union_future (ℓ c r : ℕ) (hr : r ≤ ℓ) :
    future n c ℓ ∪ future n (c + ℓ) r = future n c (ℓ + r) := by
  ext e
  simp only [future, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-! ### The cores -/

variable {P : Params} {A : ℕ → Finset (Fin n)} {σ : ℕ → ℕ} {k : ℕ}

theorem oldCore_subset (hg : Good P A σ) (i : ℕ) : oldCore n P.ℓ A i ⊆ arrivedPrefix n (i * P.ℓ) := by
  unfold oldCore
  split_ifs with hi
  · exact Finset.empty_subset _
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hj : j + 1 - 1 = j := by omega
    rw [hj, Finset.union_subset_iff]
    have he : (j + 1) * P.ℓ = j * P.ℓ + P.ℓ := by ring
    rw [he]
    exact ⟨(hg j).2.1.trans (arrivedPrefix_mono (by omega)), future_subset _ _⟩

theorem card_oldCore_le (hg : Good P A σ) (i : ℕ) : (oldCore n P.ℓ A i).card ≤ P.κ + P.ℓ := by
  unfold oldCore
  split_ifs with hi
  · simp
  · exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (hg (i - 1)).2.2 (card_future_le _ _))

theorem operations_le_max (C A : Finset (Fin n)) : operations C A ≤ max C.card A.card :=
  max_le_max (Finset.card_le_card Finset.sdiff_subset) (Finset.card_le_card Finset.sdiff_subset)

theorem operations_le (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) :
    operations (oldCore n P.ℓ A i) (A i) ≤ k := by
  have h1 := operations_le_max (oldCore n P.ℓ A i) (A i)
  have h2 := card_oldCore_le hg i
  have h3 := (hg i).2.2
  have h4 := hP.budget
  omega

/-- The transition of block `i` is finished at the end of the selected subblock. -/
theorem done_complete (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) {r : ℕ}
    (hr : hi P.ℓ P.h (σ i) ≤ r) :
    done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r =
      operations (oldCore n P.ℓ A i) (A i) := by
  apply done_of_hi_le hr
  have h1 := operations_le hP hg i
  have h2 := hP.complete
  have h3 := Nat.mul_le_mul_left P.s (div_le_hi_sub_lo P.ℓ P.h (σ i))
  omega

/-! ### The states of a block -/

theorem state_zero (i : ℕ) : state P A σ i 0 = oldCore n P.ℓ A i := by
  have hd : done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) 0 = 0 := by
    simp [done, elapsed]
  have hb : block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + 0) = ∅ := by
    rw [block_inter _ _ _ (Nat.zero_le _)]
    ext e
    simp [future]
  rw [state, hd, path_zero, hb, Finset.union_empty]

/-- At the end of block `i` the algorithm holds `A_i ∪ B_{i+1}`, the old core of
the next block. -/
theorem state_last (hP : P.Valid k) (hg : Good P A σ) (i : ℕ) :
    state P A σ i P.ℓ = oldCore n P.ℓ A (i + 1) := by
  have hd := done_complete hP hg i (hi_le P.ℓ P.h (hg i).1)
  rw [state, hd, path_of_operations_le _ _ le_rfl, block_inter _ _ _ le_rfl]
  simp [oldCore, block]

theorem state_subset (hg : Good P A σ) (i r : ℕ) :
    state P A σ i r ⊆ arrivedPrefix n (i * P.ℓ + r) := by
  rw [state, Finset.union_subset_iff]
  refine ⟨(path_subset _ _ _).trans ?_, Finset.inter_subset_right⟩
  rw [Finset.union_subset_iff]
  exact ⟨(oldCore_subset hg i).trans (arrivedPrefix_mono (by omega)),
    (hg i).2.1.trans (arrivedPrefix_mono (by omega))⟩

theorem card_state_le (hP : P.Valid k) (hg : Good P A σ) (i r : ℕ) :
    (state P A σ i r).card ≤ k := by
  have h1 := Finset.card_union_le
    (path (oldCore n P.ℓ A i) (A i)
      (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r))
    (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r))
  have h2 := card_path_le (oldCore n P.ℓ A i) (A i)
    (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r)
  have h3 : (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r)).card ≤ P.ℓ :=
    (Finset.card_le_card Finset.inter_subset_left).trans (card_future_le _ _)
  have h4 := card_oldCore_le hg i
  have h5 := (hg i).2.2
  have h6 := hP.budget
  rw [state]
  omega

/-- Each update changes at most `2s + 1` elements: at most `s` operations, each
changing two elements, and the new arrival. -/
theorem recourse_state_succ (i r : ℕ) :
    recourse (state P A σ i (r + 1)) (state P A σ i r) ≤ 2 * P.s + 1 := by
  refine (recourse_union_le _ _ _ _).trans ?_
  have hmono := done_mono P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i)
    (Nat.le_add_right r 1)
  have hpath := recourse_path_le (oldCore n P.ℓ A i) (A i) hmono
  have hsucc := done_succ_le P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r
  have harr := recourse_arrival_le (block n P.ℓ i) (i * P.ℓ + r)
  rw [show i * P.ℓ + (r + 1) = i * P.ℓ + r + 1 by ring]
  omega

/-! ### Times and blocks -/

/-- Time `u + 1` is update `u % ℓ + 1` of block `u / ℓ`. -/
theorem run_succ (u : ℕ) :
    run P A σ (u + 1) = state P A σ (u / P.ℓ) (u % P.ℓ + 1) := by
  have hd := Nat.div_add_mod' u P.ℓ
  simp only [run, pos, phase, Nat.add_sub_cancel]
  congr 1
  omega

/-- Time `u` is the state after `u % ℓ` updates of block `u / ℓ`. At the end of a
block this uses that the transition has finished. -/
theorem run_eq (hP : P.Valid k) (hg : Good P A σ) (u : ℕ) :
    run P A σ u = state P A σ (u / P.ℓ) (u % P.ℓ) := by
  have hℓ := hP.block_pos
  have hd := Nat.div_add_mod' u P.ℓ
  have hm := Nat.mod_lt u hℓ
  simp only [run, pos, phase]
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu
    simp
  rcases Nat.eq_zero_or_pos (u % P.ℓ) with hq | hq
  · -- `u = i ℓ` with `i ≥ 1`: the end of block `i - 1`.
    obtain ⟨j, hj⟩ : ∃ j, u / P.ℓ = j + 1 := ⟨u / P.ℓ - 1, by
      rcases Nat.eq_zero_or_pos (u / P.ℓ) with h0 | h0
      · rw [h0, hq] at hd
        omega
      · omega⟩
    have hu' : u = j * P.ℓ + P.ℓ := by
      rw [hj, hq] at hd
      linarith
    have hdiv : (u - 1) / P.ℓ = j := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul]
        omega
    rw [hdiv, hj, hq, state_zero, ← state_last hP hg j]
    congr 1
    omega
  · have hdiv : (u - 1) / P.ℓ = u / P.ℓ := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul]
        omega
    rw [hdiv]
    congr 1
    omega

/-- Algorithm 1 is feasible: it starts empty, holds at most `k` arrived elements,
and changes at most `2s + 1` elements per update. -/
theorem feasible_run (hP : P.Valid k) (hg : Good P A σ) :
    FeasibleTrajectory k (2 * P.s + 1) (fun t : Fin (n + 1) => run P A σ t.val) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun u => ?_⟩
  · show run P A σ 0 = ∅
    have h := run_eq hP hg 0
    rw [Nat.zero_div, Nat.zero_mod, state_zero] at h
    rw [h]
    simp [oldCore]
  · show run P A σ t.val ⊆ arrivedPrefix n t.val
    rw [run_eq hP hg]
    have := state_subset hg (t.val / P.ℓ) (t.val % P.ℓ)
    rwa [Nat.div_add_mod'] at this
  · show (run P A σ t.val).card ≤ k
    rw [run_eq hP hg]
    exact card_state_le hP hg _ _
  · show recourse (run P A σ (u.val + 1)) (run P A σ u.val) ≤ 2 * P.s + 1
    rw [run_succ, run_eq hP hg]
    exact recourse_state_succ _ _

/-- Outside the selected subblock the algorithm holds a full core: before it,
the old core `A_{i-1} ∪ B_i`; after it, the new core `A_i`; in both cases with
the arrivals `R` of the current block so far. -/
theorem value_le_run (hP : P.Valid k) (hg : Good P A σ) (f : Objective n) (u : ℕ) :
    (if u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) then
        f.value (oldCore n P.ℓ A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) +
      (if ¬ u % P.ℓ + 1 ≤ lo P.ℓ P.h (σ (u / P.ℓ)) ∧
          hi P.ℓ P.h (σ (u / P.ℓ)) ≤ u % P.ℓ + 1 then
        f.value (A (u / P.ℓ) ∪ future n (u / P.ℓ * P.ℓ) (u % P.ℓ + 1)) else 0) ≤
      f.value (run P A σ (u + 1)) := by
  have hℓ := hP.block_pos
  have hr : u % P.ℓ + 1 ≤ P.ℓ := Nat.mod_lt u hℓ
  rw [run_succ, state, block_inter _ _ _ hr]
  set i := u / P.ℓ
  set r := u % P.ℓ + 1
  by_cases h1 : r ≤ lo P.ℓ P.h (σ i)
  · rw [if_pos h1, if_neg (fun h => h.1 h1), add_zero, done_of_le_lo h1, path_zero]
  · rw [if_neg h1, zero_add]
    split_ifs with h2
    · rw [done_complete hP hg i h2.2, path_of_operations_le _ _ le_rfl]
    · exact f.nonnegative _

end ConsistentSubmodular.Checkpoints
