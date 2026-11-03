module

public import Mathlib

@[expose] public section

/-! A fixed-size threshold compression of a finite monotone baseline. Repeated
retained times are permitted, so its size bound has no enumeration overhead. -/

noncomputable section
namespace ConsistentSubmodular
namespace BaselineBins

variable (b : ℕ → ℝ) (T : ℕ) (width : ℝ)

def candidates (j : ℕ) : Finset ℕ :=
  insert T ((Finset.range (T + 1)).filter fun t => (j : ℝ) * width ≤ b t)

def first (j : ℕ) : ℕ := (candidates b T width j).min'
  (Finset.insert_nonempty _ _)

theorem first_mem (j : ℕ) : first b T width j ∈ candidates b T width j :=
  Finset.min'_mem _ _

theorem first_le_terminal (j : ℕ) : first b T width j ≤ T :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem first_le (j t : ℕ) (ht : t ≤ T) (hc : (j : ℝ) * width ≤ b t) :
    first b T width j ≤ t := by
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩)

theorem first_mono (hw : 0 ≤ width) : Monotone (first b T width) := by
  intro i j hij
  apply Finset.min'_le
  have hm := first_mem b T width j
  rcases Finset.mem_insert.mp hm with he | hm
  · exact Finset.mem_insert.mpr (Or.inl he)
  · apply Finset.mem_insert_of_mem
    have hh := (Finset.mem_filter.mp hm)
    refine Finset.mem_filter.mpr ⟨hh.1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hw).trans hh.2

theorem first_zero (hb : 0 ≤ b 0) : first b T width 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact first_le b T width 0 0 (Nat.zero_le _) (by simpa using hb)

theorem threshold_at_first (j t : ℕ) (ht : t ≤ T) (hc : (j : ℝ) * width ≤ b t) :
    (j : ℝ) * width ≤ b (first b T width j) := by
  have hm := first_mem b T width j
  rcases Finset.mem_insert.mp hm with he | hm
  · have hle := first_le b T width j t ht hc
    have : t = T := by omega
    simpa [he, this] using hc
  · exact (Finset.mem_filter.mp hm).2

/-- The last slot is reserved for the terminal endpoint. -/
def retained (N j : ℕ) : ℕ := if j < 3 * N + 1 then first b T width j else T

theorem retained_mono (N : ℕ) (hw : 0 ≤ width) : Monotone (retained b T width N) := by
  intro i j hij
  unfold retained
  split_ifs with hi hj
  · exact first_mono b T width hw hij
  · exact first_le_terminal b T width i
  · omega
  · rfl

@[simp] theorem retained_initial (N : ℕ) (hb : 0 ≤ b 0) : retained b T width N 0 = 0 := by
  simp [retained, first_zero b T width hb]

@[simp] theorem retained_terminal (N : ℕ) : retained b T width N (3 * N + 1) = T := by
  simp [retained]

theorem retained_le_terminal (N j : ℕ) : retained b T width N j ≤ T := by
  unfold retained
  split_ifs
  · exact first_le_terminal b T width j
  · rfl

/-- Every low-baseline time follows a retained time within one bin width. -/
theorem approximates (N : ℕ) (hN : 0 < N) (V : ℝ) (hV : 0 < V)
    (hb : ∀ t, 0 ≤ b t) (t : ℕ) (ht : t ≤ T) (hlow : b t < 3 * V) :
    ∃ j : Fin (3 * N + 2), retained b T (V / N) N j.val ≤ t ∧
      b t < b (retained b T (V / N) N j.val) + V / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < V / N := div_pos hV hNr
  let j := ⌊b t / (V / N)⌋₊
  have hratio : 0 ≤ b t / (V / N) := div_nonneg (hb t) hw.le
  have hj : j < 3 * N := by
    apply (Nat.floor_lt hratio).2
    apply (div_lt_iff₀ hw).2
    have hmul : ((3 * N : ℕ) : ℝ) * (V / N) = 3 * V := by push_cast; field_simp
    rwa [hmul]
  have hfloor := Nat.floor_le hratio
  have hceil := Nat.lt_floor_add_one (b t / (V / N))
  have hc : (j : ℝ) * (V / N) ≤ b t := (le_div_iff₀ hw).mp hfloor
  have hu : b t < ((j : ℝ) + 1) * (V / N) := (div_lt_iff₀ hw).mp hceil
  refine ⟨⟨j, by omega⟩, ?_, ?_⟩
  · simpa [retained, show j < 3 * N + 1 by omega] using first_le b T (V / N) j t ht hc
  · have hh := threshold_at_first b T (V / N) j t ht hc
    simp only [retained, show j < 3 * N + 1 by omega, if_pos]
    nlinarith only [hu, hh]

end BaselineBins
end ConsistentSubmodular
