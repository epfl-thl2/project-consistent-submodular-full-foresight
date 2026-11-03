module

public import ConsistentSubmodular.Deterministic.Basic.Paths

@[expose] public section

/-! Uniform finite subdivisions preserve every original node and every path
property, including the explicit node condition of a zero-piece path. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

variable {m : ℕ}

def typeL1 (p q : Point m) : ℝ := ∑ i, |p i - q i|

theorem typeL1_simplex_le_two {p q : Point m} (hp : IsSimplex p) (hq : IsSimplex q) :
    typeL1 p q ≤ 2 := by
  calc
    typeL1 p q ≤ ∑ i, (p i + q i) := by
      apply Finset.sum_le_sum
      intro i _
      exact abs_le.mpr ⟨by linarith [hp.1 i, hq.1 i], by linarith [hp.1 i, hq.1 i]⟩
    _ = 2 := by rw [Finset.sum_add_distrib, hp.2, hq.2]; norm_num

theorem typeL1_mix (p q : Point m) (x y : ℝ) :
    typeL1 (mix p q x) (mix p q y) = |x - y| * typeL1 p q := by
  unfold typeL1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : mix p q x i - mix p q y i = (x - y) * (q i - p i) := by unfold mix; ring
  rw [he, abs_mul, abs_sub_comm (q i)]

namespace PolygonalPath

/-- Uniformly divide every old segment into `N` pieces. -/
def subdivide (γ : PolygonalPath m) (N : ℕ) : PolygonalPath m where
  pieces := γ.pieces * N
  node := fun j => if h : j.val / N < γ.pieces then
    mix (γ.node ⟨j.val / N, by omega⟩) (γ.node ⟨j.val / N + 1, by omega⟩)
      (((j.val % N : ℕ) : ℝ) / N)
    else γ.node (Fin.last γ.pieces)

@[simp] theorem subdivide_pieces (γ : PolygonalPath m) (N : ℕ) :
    (γ.subdivide N).pieces = γ.pieces * N := rfl

theorem subdivide_terminal (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).node (Fin.last (γ.subdivide N).pieces) = γ.node (Fin.last γ.pieces) := by
  simp [subdivide, Nat.mul_div_cancel _ hN]

/-- The right endpoint of a refined segment is represented using its old
segment, also when it coincides with the next old node. -/
theorem subdivide_node_in_segment (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (a : Fin γ.pieces) (r : ℕ) (hr : r ≤ N) :
    (γ.subdivide N).node ⟨a.val * N + r, by
      dsimp only [subdivide_pieces]
      have := a.isLt
      nlinarith⟩ = mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) := by
  by_cases hrN : r < N
  · have hdiv : (a.val * N + r) / N = a.val := by
      rw [Nat.mul_comm a.val N, Nat.mul_add_div hN, Nat.div_eq_of_lt hrN, Nat.add_zero]
    have hmod : (a.val * N + r) % N = r := by simp [Nat.add_mod, Nat.mod_eq_of_lt hrN]
    simp only [subdivide, hdiv, a.isLt, dite_true, hmod]
    rfl
  · have hrEq : r = N := by omega
    subst r
    have hdiv : (a.val * N + N) / N = a.val + 1 := by
      have he : a.val * N + N = (a.val + 1) * N := by ring
      rw [he, Nat.mul_div_cancel _ hN]
    have hmod : (a.val * N + N) % N = 0 := by simp
    have hnR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    simp only [subdivide, hdiv, hmod, Nat.cast_zero, zero_div, mix_zero, div_self hnR,
      mix_one]
    split_ifs with ha
    · rfl
    · congr 1
      apply Fin.ext
      have := a.isLt
      simp only [Fin.val_last, Fin.val_succ]
      omega

theorem subdivide_original_node (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (i : Fin (γ.pieces + 1)) :
    (γ.subdivide N).node ⟨i.val * N, by
      dsimp only [subdivide_pieces]
      have := i.isLt
      nlinarith⟩ = γ.node i := by
  by_cases hi : i.val < γ.pieces
  · simpa using γ.subdivide_node_in_segment N hN ⟨i.val, hi⟩ 0 (Nat.zero_le N)
  · have he : i.val = γ.pieces := by omega
    have hl : i = Fin.last γ.pieces := Fin.ext he
    subst i
    exact γ.subdivide_terminal N hN

theorem subdivide_initial (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).node 0 = γ.node 0 := by
  simpa using γ.subdivide_original_node N hN 0

/-- Both endpoints of each new edge are points in the same old edge. -/
theorem subdivide_edge (γ : PolygonalPath m) (N : ℕ) (hN : 0 < N)
    (j : Fin (γ.subdivide N).pieces) :
    ∃ (a : Fin γ.pieces) (r : ℕ), r < N ∧
      (γ.subdivide N).node j.castSucc =
        mix (γ.node a.castSucc) (γ.node a.succ) ((r : ℝ) / N) ∧
      (γ.subdivide N).node j.succ =
        mix (γ.node a.castSucc) (γ.node a.succ) (((r : ℝ) + 1) / N) := by
  have hj : j.val < γ.pieces * N := j.isLt
  have ha : j.val / N < γ.pieces := (Nat.div_lt_iff_lt_mul hN).mpr hj
  let a : Fin γ.pieces := ⟨j.val / N, ha⟩
  let r := j.val % N
  have hr : r < N := Nat.mod_lt _ hN
  have he : a.val * N + r = j.val := by
    dsimp [a, r]
    simpa [Nat.mul_comm] using Nat.div_add_mod j.val N
  refine ⟨a, r, hr, ?_, ?_⟩
  · have h := γ.subdivide_node_in_segment N hN a r (Nat.le_of_lt hr)
    have hidx : (⟨a.val * N + r, by have := a.isLt; dsimp only [subdivide_pieces]; nlinarith⟩ :
        Fin ((γ.subdivide N).pieces + 1)) = j.castSucc := Fin.ext he
    rwa [hidx] at h
  · have h := γ.subdivide_node_in_segment N hN a (r + 1) (by omega)
    have hidx : (⟨a.val * N + (r + 1), by have := a.isLt; dsimp only [subdivide_pieces]; nlinarith⟩ :
        Fin ((γ.subdivide N).pieces + 1)) = j.succ := by apply Fin.ext; simp only [Fin.val_succ]; omega
    rw [hidx, Nat.cast_add, Nat.cast_one] at h
    exact h

theorem Along.subdivide {γ : PolygonalPath m} {Φ : Point m → Prop}
    (hγ : γ.Along Φ) (N : ℕ) (hN : 0 < N) : (γ.subdivide N).Along Φ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro j
    by_cases hj : j.val < (γ.subdivide N).pieces
    · obtain ⟨a, r, hr, he, _⟩ := γ.subdivide_edge N hN ⟨j.val, hj⟩
      have hjcast : (⟨j.val, hj⟩ : Fin (γ.subdivide N).pieces).castSucc = j := Fin.ext rfl
      rw [hjcast] at he
      rw [he]
      apply hγ.2 a _ (div_nonneg (Nat.cast_nonneg _) hn.le)
      apply (div_le_one hn).mpr
      exact_mod_cast Nat.le_of_lt hr
    · have he : j = Fin.last (γ.subdivide N).pieces := Fin.ext (by simp only [Fin.val_last]; have := j.isLt; omega)
      rw [he, γ.subdivide_terminal N hN]
      exact hγ.1 _
  · intro j x hx hx'
    obtain ⟨a, r, hr, hl, hu⟩ := γ.subdivide_edge N hN j
    rw [hl, hu, mix_mix]
    apply hγ.2 a
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hx') (by positivity))
        (mul_nonneg hx (by positivity))
    · have hb : ((r : ℝ) + 1) / N ≤ 1 := by
        apply (div_le_one hn).mpr
        exact_mod_cast (show r + 1 ≤ N by omega)
      have ha : (r : ℝ) / N ≤ 1 := by
        apply (div_le_one hn).mpr
        exact_mod_cast Nat.le_of_lt hr
      nlinarith [mul_nonneg (sub_nonneg.mpr hx') (sub_nonneg.mpr ha),
        mul_nonneg hx (sub_nonneg.mpr hb)]

theorem subdivide_step_le (γ : PolygonalPath m)
    (hγ : ∀ i, IsSimplex (γ.node i)) (N : ℕ) (hN : 0 < N)
    (j : Fin (γ.subdivide N).pieces) :
    typeL1 ((γ.subdivide N).node j.castSucc) ((γ.subdivide N).node j.succ) ≤ 2 / N := by
  obtain ⟨a, r, hr, hl, hu⟩ := γ.subdivide_edge N hN j
  rw [hl, hu, typeL1_mix]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have habs : |(r : ℝ) / N - ((r : ℝ) + 1) / N| = 1 / N := by
    have he : (r : ℝ) / N - ((r : ℝ) + 1) / N = -(1 / N) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  rw [habs]
  have h := mul_le_mul_of_nonneg_left (typeL1_simplex_le_two (hγ a.castSucc) (hγ a.succ))
    (show (0 : ℝ) ≤ 1 / N by positivity)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using h

def length (γ : PolygonalPath m) : ℝ :=
  ∑ j : Fin γ.pieces, typeL1 (γ.node j.castSucc) (γ.node j.succ)

theorem subdivide_length_le (γ : PolygonalPath m)
    (hγ : ∀ i, IsSimplex (γ.node i)) (N : ℕ) (hN : 0 < N) :
    (γ.subdivide N).length ≤ 2 * γ.pieces := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => γ.subdivide_step_le hγ N hN j)
  change (γ.subdivide N).length ≤ _ at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    subdivide_pieces] at h
  simp only [Fintype.card_eq_nat_card, Nat.card_fin] at h
  change (γ.subdivide N).length ≤ ((γ.pieces * N : ℕ) : ℝ) * (2 / N) at h
  rw [Nat.cast_mul] at h
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (γ.pieces : ℝ) * N * (2 / N) = 2 * γ.pieces := by field_simp
  rwa [he] at h

end PolygonalPath

end ConsistentSubmodular
