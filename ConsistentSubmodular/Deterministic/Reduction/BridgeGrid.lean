module

public import ConsistentSubmodular.Deterministic.Reduction.Bridge
public import ConsistentSubmodular.Deterministic.Reduction.TypeLipschitz
public import ConsistentSubmodular.Deterministic.Reduction.PathSubdivision
public import ConsistentSubmodular.Deterministic.Reduction.ForcedSet

@[expose] public section

/-! A uniform two-core grid and a bounded forced set for its rounding. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace BridgeGrid

variable {n : ℕ}

def point (K : ℕ) (j : Fin (K + 1)) : Point 1 :=
  mix (vertex 0) (vertex 1) ((j.val : ℝ) / K)

theorem simplex (K : ℕ) (hK : 0 < K) (j : Fin (K + 1)) : IsSimplex (point K j) := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  apply (simplex_vertex _).mix (simplex_vertex _) (by positivity)
  apply (div_le_one hk).mpr
  exact_mod_cast (show j.val ≤ K by omega)

@[simp] theorem initial (K : ℕ) : point K 0 = vertex 0 := by simp [point]
@[simp] theorem terminal (K : ℕ) (hK : 0 < K) : point K (Fin.last K) = vertex 1 := by
  simp [point, ne_of_gt (show (0 : ℝ) < K by exact_mod_cast hK)]

theorem step (K : ℕ) (hK : 0 < K) (j : Fin K) :
    typeL1 (point K j.castSucc) (point K j.succ) ≤ 2 / K := by
  rw [point, point, typeL1_mix]
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have he : |((j.castSucc.val : ℕ) : ℝ) / K - ((j.succ.val : ℕ) : ℝ) / K| = 1 / K := by
    simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have he : (j.val : ℝ) / K - ((j.val : ℝ) + 1) / K = -(1 / K) := by ring
    rw [he, abs_neg, abs_of_nonneg (by positivity)]
  rw [he]
  have h := mul_le_mul_of_nonneg_left
    (typeL1_simplex_le_two (simplex_vertex (0 : Fin 2)) (simplex_vertex (1 : Fin 2)))
    (show (0 : ℝ) ≤ 1 / K by positivity)
  convert h using 1
  ring

theorem total_step (K : ℕ) (hK : 0 < K) :
    (∑ j : Fin K, typeL1 (point K j.castSucc) (point K j.succ)) ≤ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => step K hK j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have he : (K : ℝ) * (2 / K) = 2 := by field_simp
  rwa [he] at h

theorem type_value (f : Objective n) (A B Q : Finset (Fin n))
    (V : ℝ) (hV : 0 ≤ V) (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B))
    (K : ℕ) (hK : 0 < K) (j : Fin (K + 1)) :
    (3 : ℝ) / 4 * V ≤ finiteExpectation (point K j) (f.onTypes ![A, B] Q).value := by
  apply (f.onTypes ![A, B] Q).two_vertex_bridge 0 1 (by decide) V hV
    (by simpa using hA) (by simpa using hB)
  · positivity
  · apply (div_le_one (show (0 : ℝ) < K by exact_mod_cast hK)).mpr
    exact_mod_cast (show j.val ≤ K by omega)

/-- A global union-value bound suffices for a bounded forced set; no
cardinality optimum is needed in the two-core bridge. -/
theorem forced_set (f : Objective n) (U : Finset (Fin n)) (H : ℕ) (hH : 0 < H)
    (V : ℝ) (hV : 0 < V) (hU : f.value U ≤ 2 * V) :
    ∃ D ⊆ U, D.card ≤ H ∧ ∀ e ∈ U, e ∉ D →
      f.value (insert e D) - f.value D ≤ 2 * V / H := by
  obtain ⟨D, hDU, hins, hrem⟩ := f.exists_penalized_core U (2 * V / H)
  refine ⟨D, hDU, ?_, hins⟩
  have hs : (∑ _e ∈ D, 2 * V / (H : ℝ)) ≤ ∑ e ∈ D, (f.value D - f.value (D.erase e)) := by
    exact Finset.sum_le_sum (fun e he => (hrem e he).le)
  have hsum := f.sum_removal_marginals_le D
  have hv := (f.monotone _ _ hDU).trans hU
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hpos : (0 : ℝ) < 2 * V / H := by positivity
  have hcancel : (H : ℝ) * (2 * V / H) = 2 * V := by field_simp
  have hbound : (D.card : ℝ) * (2 * V / H) ≤ (H : ℝ) * (2 * V / H) := by
    rw [hcancel]
    linarith [f.nonnegative ∅]
  exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp hbound

end BridgeGrid
end ConsistentSubmodular
