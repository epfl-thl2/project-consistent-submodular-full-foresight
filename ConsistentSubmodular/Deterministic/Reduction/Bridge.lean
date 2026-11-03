module

public import ConsistentSubmodular.Deterministic.Basic.PhysicalSampling
public import ConsistentSubmodular.Deterministic.Basic.CompatibleProfiles
public import ConsistentSubmodular.Deterministic.Basic.Paths

@[expose] public section

/-! A two-core bridge under a fixed buffer. The universal three-quarter bound
uses only monotonicity and nonnegativity, so duplicate physical cores are safe. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace Objective

variable {m n : ℕ}
theorem two_vertex_bridge (f : Objective (m + 1)) (a b : Fin (m + 1)) (hab : a ≠ b)
    (V : ℝ) (hV : 0 ≤ V) (ha : V ≤ f.value {a}) (hb : V ≤ f.value {b})
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (3 : ℝ) / 4 * V ≤ finiteExpectation (mix (vertex a) (vertex b) x) f.value := by
  classical
  let p := mix (vertex a) (vertex b) x
  have hp : IsSimplex p := (simplex_vertex a).mix (simplex_vertex b) hx hx1
  have hc : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i => ⟨hp.1 i, hp.coordinate_le_one i⟩
  have hm := finiteExpectation_mono p hc (v := fun I => if ({a, b} ∩ I).Nonempty then V else 0)
    (w := f.value) (by
      intro I
      dsimp only
      split_ifs with hn
      · obtain ⟨i, hi⟩ := hn
        have hiI := (Finset.mem_inter.mp hi).2
        have hiab := (Finset.mem_inter.mp hi).1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiab
        rcases hiab with rfl | rfl
        · exact ha.trans (f.monotone _ _ (Finset.singleton_subset_iff.mpr hiI))
        · exact hb.trans (f.monotone _ _ (Finset.singleton_subset_iff.mpr hiI))
      · exact f.nonnegative I)
  rw [finiteExpectation_weighted_hit] at hm
  have hprod : (∏ i ∈ ({a, b}:Finset (Fin (m + 1))), (1 - p i)) = x * (1 - x) := by
    dsimp [p]
    rw [prod_mix_vertices_complement _ a b hab]
    simp
  rw [hprod] at hm
  have hquad : x * (1 - x) ≤ (1 : ℝ) / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hh := mul_nonneg hV (sub_nonneg.mpr hquad)
  dsimp [p] at hm
  nlinarith only [hm, hh]

end Objective
end ConsistentSubmodular
