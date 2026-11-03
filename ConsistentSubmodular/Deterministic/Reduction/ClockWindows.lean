module

public import ConsistentSubmodular.Deterministic.Reduction.WindowTransfer
public import ConsistentSubmodular.Deterministic.Reduction.ProtectedClock

@[expose] public section

/-! Fractional windows along a protected clock. Buffers contain all arrivals
since the old ground set was fixed, and neighboring windows use canonical
optimizer endpoints suitable for a two-core bridge. -/

noncomputable section
namespace ConsistentSubmodular
namespace ProtectedClock
variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

def windowOld (n i : ℕ) : Finset (Fin n) := arrivedPrefix n (C.start i)
def windowBuffer (n i u : ℕ) : Finset (Fin n) :=
  arrivedPrefix n (C.start i + u) \ C.windowOld n i
def windowDuration (i : ℕ) : ℕ := C.start (i + 1) - C.start i

@[simp] theorem windowBuffer_zero (n i : ℕ) : C.windowBuffer n i 0 = ∅ := by
  simp [windowBuffer, windowOld]

theorem windowBuffer_mono (n i : ℕ) : Monotone (C.windowBuffer n i) := by
  intro u v huv e he
  exact Finset.mem_sdiff.mpr ⟨arrivedPrefix_mono (Nat.add_le_add_left huv _)
    (Finset.mem_sdiff.mp he).1, (Finset.mem_sdiff.mp he).2⟩

theorem windowDuration_end (i : ℕ) : C.start i + C.windowDuration i = C.start (i + 1) :=
  Nat.add_sub_of_le (C.start_mono (Nat.le_succ i))

theorem windowBuffer_terminal (n i : ℕ) :
    C.windowBuffer n i (C.windowDuration i) = arrivedPrefix n (C.start (i + 1))\arrivedPrefix n (C.start i) := by
  simp [windowBuffer, windowOld, C.windowDuration_end]

theorem windowBuffer_absolute (n i t : ℕ) (ht : C.start i ≤ t) :
    C.windowBuffer n i (t - C.start i) = arrivedPrefix n t\arrivedPrefix n (C.start i) := by
  simp [windowBuffer, windowOld, Nat.add_sub_of_le ht]

variable {n : ℕ} (f : Objective n) (κ : ℕ)

def windowInitial (i : ℕ) : Finset (Fin n) := f.bufferedOptimizer (C.windowOld n i) ∅ κ
def windowTerminal (i : ℕ) : Finset (Fin n) :=
  f.bufferedOptimizer (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ

theorem windowInitial_spec (i : ℕ) : C.windowInitial f κ i ⊆ C.windowOld n i ∧
    (C.windowInitial f κ i).card ≤ κ ∧
    f.value (C.windowInitial f κ i) = f.prefixOptimum κ (C.start i) := by
  have hs := f.bufferedOptimizer_spec (C.windowOld n i) ∅ κ
  exact ⟨hs.1, hs.2.1, by simp [windowInitial, Objective.prefixOptimum, Objective.bufferedOptimum, windowOld]⟩

theorem windowTerminal_spec (i : ℕ) : C.windowTerminal f κ i ⊆ C.windowOld n i ∧
    (C.windowTerminal f κ i).card ≤ κ ∧
    f.value (C.windowBuffer n i (C.windowDuration i) ∪ C.windowTerminal f κ i) =
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ := by
  have hs := f.bufferedOptimizer_spec (C.windowOld n i) (C.windowBuffer n i (C.windowDuration i)) κ
  exact ⟨hs.1, hs.2.1, rfl⟩

/-- Every actual-time prefix competitor fits inside the old core plus new buffer. -/
theorem window_benchmark_dominates (i u : ℕ) :
    f.prefixOptimum κ (C.start i + u) ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i u) κ :=
  f.optimum_le_windowOptimum (C.windowOld n i) (arrivedPrefix n (C.start i + u)) κ

theorem window_benchmark_absolute (i t : ℕ) (ht : C.start i ≤ t) :
    f.prefixOptimum κ t ≤
      f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (t - C.start i)) κ := by
  have hh := C.window_benchmark_dominates f κ i (t - C.start i)
  rwa [Nat.add_sub_of_le ht] at hh

/-- Both bridge endpoints meet the next prefix scale under the protected old buffer. -/
theorem window_bridge_endpoints (i : ℕ) :
    let buffer := C.windowBuffer n i (C.windowDuration i)
    let V := f.prefixOptimum κ (C.start (i + 1))
    V ≤ f.value (buffer ∪ C.windowTerminal f κ i) ∧
    V ≤ f.value (buffer ∪ C.windowInitial f κ (i + 1)) ∧
    f.value (C.windowTerminal f κ i) ≤ V ∧
    f.value (C.windowInitial f κ (i + 1)) ≤ V := by
  dsimp only
  have ht := C.windowTerminal_spec f κ i
  have hi := C.windowInitial_spec f κ (i + 1)
  refine ⟨?_, ?_, ?_, hi.2.2.le⟩
  · rw [ht.2.2]
    have hh := C.window_benchmark_dominates f κ i (C.windowDuration i)
    rwa [C.windowDuration_end] at hh
  · rw [← hi.2.2]
    exact f.monotone _ _ Finset.subset_union_right
  · have hsub : C.windowTerminal f κ i ⊆ arrivedPrefix n (C.start (i + 1)) :=
      ht.1.trans (arrivedPrefix_mono (C.start_mono (Nat.le_succ i)))
    simpa only [Finset.empty_union] using f.le_bufferedOptimum (Q := ∅) hsub ht.2.1

theorem window_bridge_arrived (i : ℕ) :
    C.windowTerminal f κ i ∪ C.windowInitial f κ (i + 1) ⊆ arrivedPrefix n (C.start (i + 1)) := by
  apply Finset.union_subset
  · exact (C.windowTerminal_spec f κ i).1.trans (arrivedPrefix_mono (C.start_mono (Nat.le_succ i)))
  · exact (C.windowInitial_spec f κ (i + 1)).1

theorem windowBuffer_disjoint (n i u : ℕ) : Disjoint (C.windowBuffer n i u) (C.windowOld n i) :=
  Finset.sdiff_disjoint

/-- The fractional family uses exactly the prescribed initial and terminal
optimizers, including zero-scale windows. Its geometry comes from the
certificates of the compressed windows. -/
def fractionalWindows (O : CertificateFamily) (N : ℕ) (hN : 0 < N) (i : ℕ) :
    FractionalWindow f (C.windowOld n i) (C.windowBuffer n i) (C.windowBuffer_mono n i)
      κ N (C.windowDuration i) (C.windowInitial f κ i) (C.windowTerminal f κ i)
      O.level (O.budget (3 * N + 1)) := by
  apply Classical.choice
  apply f.fractional_window O _ _ _ (C.windowBuffer_zero n i) (C.windowBuffer_disjoint n i)
    κ N _ hN
  · have hs := C.windowInitial_spec f κ i
    simpa only [C.windowBuffer_zero, Finset.empty_union] using hs
  · exact C.windowTerminal_spec f κ i

/-- Retained physical tests extend to all real updates, at a uniform relative
loss. This is the checkpoint field needed by the protected global schedule. -/
theorem retained_tests_prefix (O : CertificateFamily) (N : ℕ) (hN : 0 < N) (i : ℕ)
    (A : Finset (Fin n))
    (htests : ∀ j, let W := C.fractionalWindows f κ O N hN i
      O.level * f.bufferedOptimum (C.windowOld n i) (C.windowBuffer n i (W.retained j)) κ-
        f.prefixOptimum κ (C.start i) / N ≤ f.value (C.windowBuffer n i (W.retained j) ∪ A)) :
    ∀ t, C.start i ≤ t → t ≤ C.start (i + 1) →
      (O.level - 2 / N) * f.prefixOptimum κ t ≤
        f.value (A ∪ (arrivedPrefix n t\arrivedPrefix n (C.start i))) := by
  let W := C.fractionalWindows f κ O N hN i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hη : 0 ≤ (1 : ℝ) / N := div_nonneg (by norm_num) hNr.le
  have hV : 0 ≤ f.prefixOptimum κ (C.start i) := f.prefixOptimum_nonnegative _ _
  have hext := W.retained_tests_extend hN A (f.prefixOptimum κ (C.start i) / N)
    (div_nonneg hV hNr.le) htests
  intro t ht0 ht1
  have hu : t - C.start i ≤ C.windowDuration i := Nat.sub_le_sub_right ht1 _
  have hg := hext (t - C.start i) hu
  have hbench := C.window_benchmark_absolute f κ i t ht0
  rw [C.windowBuffer_absolute n i t ht0] at hbench
  have hmono := f.prefixOptimum_monotone κ ht0
  have hscale : f.bufferedOptimum (C.windowOld n i) ∅ κ = f.prefixOptimum κ (C.start i) := rfl
  rw [hscale, C.windowBuffer_absolute n i t ht0, Finset.union_comm] at hg
  have hdiv := div_le_div_of_nonneg_right hmono hNr.le
  have hcur : 0 ≤ f.prefixOptimum κ t / N := div_nonneg (f.prefixOptimum_nonnegative _ _) hNr.le
  have hid : (O.level - 2 / N) * f.prefixOptimum κ t =
      O.level * f.prefixOptimum κ t - 2 * (f.prefixOptimum κ t / N) := by ring
  have hbench' := mul_le_mul_of_nonneg_left hbench O.level_nonneg
  have hdiv' := mul_le_mul_of_nonneg_left hdiv O.level_nonneg
  have hle := mul_le_mul_of_nonneg_right O.level_le (show 0 ≤ f.prefixOptimum κ (C.start i) / N by
    exact div_nonneg (f.prefixOptimum_nonnegative _ _) hNr.le)
  rw [hid]
  nlinarith only [hg, hbench', hdiv, hdiv', hcur, hle, mul_nonneg O.level_nonneg
    (div_nonneg (f.prefixOptimum_nonnegative κ (C.start i)) hNr.le)]

end ProtectedClock
end ConsistentSubmodular
