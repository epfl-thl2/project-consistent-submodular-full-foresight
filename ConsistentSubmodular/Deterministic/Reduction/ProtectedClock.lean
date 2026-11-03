module

public import ConsistentSubmodular.Deterministic.Reduction.SchedulingBasics

@[expose] public section

noncomputable section
namespace ConsistentSubmodular

/-- A block contains a stable interval or its last candidate already has a
fourfold increase. The proof uses only linear growth, not concentration. -/
theorem exists_protected_interval (F : ℕ → ℝ) (hF : Monotone F)
    (hF0 : ∀ t, 0 ≤ F t) (a J ell : ℕ) (hJ : 1 ≤ J)
    (η : ℝ) (hη : 0 ≤ η) (hgrowth : 3 ≤ ((J - 1 : ℕ) : ℝ) * η) :
    ∃ j : ℕ, j < J ∧
      (F (a + (j + 1) * ell) ≤ (1 + η) * F (a + j * ell) ∨
        4 * F a ≤ F (a + j * ell)) := by
  classical
  by_cases hstable : ∃ j : ℕ, j < J ∧
      F (a + (j + 1) * ell) ≤ (1 + η) * F (a + j * ell)
  · obtain ⟨j, hj, h⟩ := hstable
    exact ⟨j, hj, Or.inl h⟩
  have hinc : ∀ j : ℕ, j < J →
      (1 + η) * F (a + j * ell) ≤ F (a + (j + 1) * ell) := by
    intro j hj
    exact (lt_of_not_ge (fun h => hstable ⟨j, hj, h⟩)).le
  have hlinear : ∀ j : ℕ, j ≤ J →
      (1 + (j : ℝ) * η) * F a ≤ F (a + j * ell) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hi := ih (by omega)
      have hc := hinc j (by omega)
      have hm := hF (show a ≤ a + j * ell by omega)
      have hp := mul_le_mul_of_nonneg_left hm hη
      push_cast
      nlinarith only [hi, hc, hp]
  refine ⟨J - 1, by omega, Or.inr ?_⟩
  have hh := hlinear (J - 1) (by omega)
  have hp := mul_nonneg (sub_nonneg.mpr hgrowth) (hF0 a)
  nlinarith only [hh, hp]

structure ProtectedClock (F : ℕ → ℝ) (η : ℝ) (b ell : ℕ) where
  start : ℕ → ℕ
  lower : ∀ i, (i + 1) * b ≤ start i
  upper : ∀ i, start i + ell ≤ (i + 2) * b
  protection : ∀ i,
    F (start i + ell) ≤ (1 + η) * F (start i) ∨
      4 * F ((i + 1) * b) ≤ F (start i)

/-- Fixed choices depend only on the fully disclosed optimum sequence. -/
def protectedClock (F : ℕ → ℝ) (hF : Monotone F) (hF0 : ∀ t, 0 ≤ F t)
    (b J ell : ℕ) (hJ : 1 ≤ J) (hfit : J * ell ≤ b)
    (η : ℝ) (hη : 0 ≤ η) (hgrowth : 3 ≤ ((J - 1 : ℕ) : ℝ) * η) :
    ProtectedClock F η b ell := by
  have he (i : ℕ) := exists_protected_interval F hF hF0 ((i + 1) * b) J ell hJ η hη hgrowth
  let j := fun i => Classical.choose (he i)
  have hj (i : ℕ) : j i < J := (Classical.choose_spec (he i)).1
  refine {
    start := fun i => (i + 1) * b + j i * ell
    lower := fun i => Nat.le_add_right _ _
    upper := ?_
    protection := ?_ }
  · intro i
    have hh := Nat.mul_le_mul_right ell (show j i + 1 ≤ J by have := hj i; omega)
    nlinarith
  · intro i
    have hh := (Classical.choose_spec (he i)).2
    simpa only [j, Nat.add_mul, one_mul, Nat.add_assoc] using hh

namespace ProtectedClock

variable {F : ℕ → ℝ} {η : ℝ} {b ell : ℕ} (C : ProtectedClock F η b ell)

theorem separated (i : ℕ) : C.start i + ell ≤ C.start (i + 1) :=
  (C.upper i).trans (by simpa [Nat.add_assoc] using C.lower (i + 1))

theorem start_mono : Monotone C.start := by
  apply monotone_nat_of_le_succ
  intro i
  exact (Nat.le_add_right _ _).trans (C.separated i)

theorem transition_age (i : ℕ) : C.start (i + 1) + ell - C.start i ≤ 2 * b := by
  have hu := C.upper (i + 1)
  have hl := C.lower i
  have hsum : C.start (i + 1) + ell ≤ C.start i + 2 * b := by nlinarith
  omega

theorem previous_buffer_protected {n : ℕ} (i t : ℕ)
    (ht0 : C.start (i + 1) ≤ t) (ht1 : t ≤ C.start (i + 1) + ell) :
    arrivedPrefix n (C.start (i + 1)) \ arrivedPrefix n (C.start i) ⊆
      rollingBuffer n (4 * b) t := by
  have ha := C.transition_age i
  have hm := C.start_mono (show i ≤ i + 1 by omega)
  have hp := protected_buffer_subset (n := n) (s := C.start i) (t := t)
    (width := 4 * b) (by omega) (by omega)
  intro e he
  apply hp
  exact Finset.mem_sdiff.mpr ⟨arrivedPrefix_mono ht0 (Finset.mem_sdiff.mp he).1,
    (Finset.mem_sdiff.mp he).2⟩

theorem current_buffer_protected {n : ℕ} (i t : ℕ)
    (ht0 : C.start i ≤ t) (ht1 : t ≤ C.start (i + 1) + ell) :
    arrivedPrefix n t \ arrivedPrefix n (C.start i) ⊆ rollingBuffer n (4 * b) t := by
  have ha := C.transition_age i
  exact protected_buffer_subset ht0 (by omega)

theorem initial_buffer_full {n : ℕ} (t : ℕ) (ht : t ≤ C.start 0 + ell) :
    rollingBuffer n (4 * b) t = arrivedPrefix n t := by
  have hu := C.upper 0
  have hage : t - 4 * b = 0 := by simp only [zero_add] at hu; omega
  simp [rollingBuffer, hage, arrivedPrefix]

end ProtectedClock

namespace Objective

variable {n : ℕ} (f : Objective n)

def prefixOptimum (k t : ℕ) : ℝ := f.bufferedOptimum (arrivedPrefix n t) ∅ k

theorem prefixOptimum_monotone (k : ℕ) : Monotone (f.prefixOptimum k) := by
  intro s t hst
  exact f.bufferedOptimum_mono_ground (arrivedPrefix_mono hst)

theorem prefixOptimum_nonnegative (k t : ℕ) : 0 ≤ f.prefixOptimum k t :=
  f.bufferedOptimum_nonnegative _ _ _

theorem unstable_transition_buffer (k : ℕ) {η : ℝ} {b ell : ℕ}
    (C : ProtectedClock (f.prefixOptimum k) η b ell) (i t : ℕ)
    (ht0 : C.start i ≤ t) (ht1 : t ≤ C.start i + ell)
    (hu : 4 * f.prefixOptimum k ((i + 1) * b) ≤ f.prefixOptimum k (C.start i)) :
    (3 : ℝ) / 4 * f.prefixOptimum k t ≤ f.value (rollingBuffer n (4 * b) t) := by
  have hlow := C.lower i
  have hhigh := C.upper i
  have hg := hu.trans (f.prefixOptimum_monotone k ht0)
  have hp := f.unstable_buffer_protection (arrivedPrefix n ((i + 1) * b))
    (arrivedPrefix n t) k hg
  have hage : t - ((i + 1) * b) ≤ 4 * b := by
    have hh : t ≤ (i + 1) * b + b := by nlinarith
    omega
  have hsub := protected_buffer_subset (n := n) (s := (i + 1) * b) (t := t)
    (width := 4 * b) (by omega) hage
  exact hp.trans (f.monotone _ _ hsub)

end Objective
end ConsistentSubmodular
