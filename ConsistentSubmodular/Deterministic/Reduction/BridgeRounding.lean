module

public import ConsistentSubmodular.Deterministic.Reduction.BridgeGrid
public import ConsistentSubmodular.Deterministic.Reduction.BridgeSmall
public import ConsistentSubmodular.Deterministic.Reduction.PhysicalIntersection
public import ConsistentSubmodular.Deterministic.Reduction.JointRounding
public import ConsistentSubmodular.Deterministic.Reduction.SamplingScale
public import ConsistentSubmodular.Deterministic.Reduction.ForcedPath
public import ConsistentSubmodular.Deterministic.Reduction.RoundingBudget

@[expose] public section

/-! A uniform rounded bridge between arbitrary feasible old cores. -/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular

set_option maxHeartbeats 2000000

/-- The forced-element reserve of a bridge with `2N + 1` grid points. -/
def bridgeHeavy (N : ℕ) : ℕ := 8 * N ^ 2 * logBudget (4 * (2 * N + 1))

namespace Objective
variable {n : ℕ} (f : Objective n)

theorem exists_rounded_bridge_large (A B Q : Finset (Fin n)) (N κ : ℕ) (V : ℝ)
    (hN : 0 < N) (hκ : bridgeHeavy N ≤ κ) (hV : 0 < V)
    (hAc : A.card ≤ κ) (hBc : B.card ≤ κ) (hAv : f.value A ≤ V) (hBv : f.value B ≤ V)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧ P.length ≤ 10 * κ ∧
      ∀ j, P.node j ⊆ A ∪ B ∧ ((P.node j).card : ℝ) ≤ κ + (κ : ℝ) / N + bridgeHeavy N ∧
        ((3 : ℝ) / 4 - 2 / N) * V ≤ f.value (Q ∪ P.node j) := by
  classical
  let K := 2 * N
  let H := bridgeHeavy N
  let U := A ∪ B
  let cores : Fin 2 → Finset (Fin n) := ![A, B]
  let z := fun j : Fin (K + 1) => physicalProbability cores (BridgeGrid.point K j)
  have hK : 0 < K := by dsimp [K]; omega
  have hH : 0 < H := by
    have := one_le_logBudget (4 * (2 * N + 1))
    dsimp [H, bridgeHeavy]; positivity
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (0 : ℝ) < H := by exact_mod_cast hH
  have hk : (0 : ℝ) < κ := by exact_mod_cast lt_of_lt_of_le hH hκ
  have hdim : (0 : ℝ) < K + 1 := by positivity
  have hU : f.value U ≤ 2 * V := by
    have h := f.subadditive A B
    dsimp [U]
    linarith
  obtain ⟨D, hDU, hDcard, hDcap⟩ := BridgeGrid.forced_set f U H hH V hV hU
  let g := f.contractOn U (D ∪ Q)
  have hcores (i : Fin 2) : (cores i).card ≤ κ := by fin_cases i <;> assumption
  have hcoreV (i : Fin 2) : f.value (cores i) ≤ V := by fin_cases i <;> assumption
  have hz (j : Fin (K + 1)) (e : Fin n) : 0 ≤ z j e ∧ z j e ≤ 1 :=
    physicalProbability_mem_unitInterval cores _ (BridgeGrid.simplex K hK j) e
  have hsupport (j : Fin (K + 1)) (e : Fin n) (he : e ∉ U) : z j e = 0 := by
    have heA : e ∉ A := fun h => he (Finset.mem_union_left B h)
    have heB : e ∉ B := fun h => he (Finset.mem_union_right A h)
    simp [z, cores, physicalProbability, Fin.sum_univ_two, heA, heB]
  have hmincube (j : Fin K) (e : Fin n) :
      0 ≤ min (z j.castSucc e) (z j.succ e) ∧ min (z j.castSucc e) (z j.succ e) ≤ 1 :=
    ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
  have hsize (j : Fin (K + 1)) : (∑ e, z j e) ≤ κ :=
    physicalProbability_total_le cores _ (BridgeGrid.simplex K hK j).1
      (BridgeGrid.simplex K hK j).2.le hcores
  have hmean (j : Fin K) :
      finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) g.value ≤ 2 * V := by
    have hp (S : Finset (Fin n)) : g.value S ≤ 2 * V :=
      (f.contractOn_le U (D ∪ Q) S).trans ((f.monotone _ _ Finset.inter_subset_right).trans hU)
    simpa only [finiteExpectation_const] using finiteExpectation_mono _ (hmincube j) hp
  have htotal : (∑ j : Fin K, ∑ e, |z j.castSucc e - z j.succ e|) ≤ 2 * κ := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun (j : Fin K) _ =>
      physicalProbability_l1_le cores (BridgeGrid.point K j.castSucc)
        (BridgeGrid.point K j.succ) hcores)
    change (∑ j : Fin K, ∑ e, |z j.castSucc e - z j.succ e|) ≤
      ∑ j : Fin K, (κ : ℝ) * typeL1 (BridgeGrid.point K j.castSucc) (BridgeGrid.point K j.succ) at hs
    rw [← Finset.mul_sum] at hs
    have hb := mul_le_mul_of_nonneg_left (BridgeGrid.total_step K hK) hk.le
    nlinarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = logBudget (4 * (K + 1)) := ⟨_, rfl⟩
  have hc : 4 * (K + 1) ≤ 2 ^ c := hcdef ▸ (lt_two_pow_logBudget _).le
  have hHeq : H = 8 * N ^ 2 * c := by rw [hcdef]; rfl
  have hlarge : 4 * (N : ℝ) ^ 2 * c ≤ κ := by
    have hHκ : H ≤ κ := hκ
    have h4 : 4 * N ^ 2 * c ≤ H := by
      rw [hHeq]
      exact Nat.mul_le_mul_right c (Nat.mul_le_mul_right (N ^ 2) (by norm_num))
    exact_mod_cast h4.trans hHκ
  have hsizeBudget : Real.exp (-(((κ : ℝ) / N) ^ 2) / (4 * κ)) ≤ 1 / (4 * ((K : ℝ) + 1)) := by
    have h := RoundingBudget.size_budget_exp (K + 1) N c κ (by omega) hN hc hlarge hk
    push_cast at h
    exact h
  have hvalueBudget : Real.exp (-((V / N) ^ 2) / (2 * (2 * V / H) * (2 * V))) ≤ 1 / (4 * ((K : ℝ) + 1)) := by
    have h := RoundingBudget.bridge_value_budget_exp (K + 1) N c H V (by omega) hN hV hH hc
      hHeq.ge
    push_cast at h
    exact h
  have hb2 : (κ : ℝ) / N ≤ 2 * κ := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have := div_le_self hk.le hN1
    linarith
  have hbudget : ((K + 1 : ℕ) : ℝ) * (1 / (4 * ((K : ℝ) + 1)))+
      (Fintype.card (Fin K) : ℝ) * (1 / (4 * ((K : ℝ) + 1))) + (1 : ℝ) / 4 < 1 := by
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact RoundingBudget.union_budget _ _ _ hdim le_rfl (by linarith)
  obtain ⟨S, hzero, hone, hcards, hvalues, hcost, _⟩ := exists_joint_rounding z hz
    (fun _j : Fin K => g) Fin.castSucc Fin.succ Fin.castSucc Fin.succ
    (κ : ℝ) (2 * V / H) (2 * V) (V / N) ((κ : ℝ) / N) (8 * κ)
    (1 / (4 * ((K : ℝ) + 1))) (1 / (4 * ((K : ℝ) + 1))) ((1 : ℝ) / 4)
    (by positivity) (by positivity) hb2 (by positivity) (by positivity) (by positivity)
    hsize (fun _ => f.contractOn_singleton_cap U D Q (by positivity) hDcap)
    hmean hsizeBudget hvalueBudget (by nlinarith) hbudget
  have hSU (j) : S j ⊆ U := by
    intro e he
    by_contra heU
    exact hzero j e (hsupport j e heU) he
  have hS0 : S 0 = A := by
    ext e
    have heq : z 0 e = if e ∈ A then 1 else 0 := by
      change physicalProbability cores (BridgeGrid.point K 0) e = if e ∈ A then 1 else 0
      rw [BridgeGrid.initial, physicalProbability_vertex]
      rfl
    by_cases he : e ∈ A
    · exact iff_of_true (hone 0 e (by simpa [he] using heq)) he
    · exact iff_of_false (hzero 0 e (by simpa [he] using heq)) he
  have hS1 : S (Fin.last K) = B := by
    ext e
    have heq : z (Fin.last K) e = if e ∈ B then 1 else 0 := by
      change physicalProbability cores (BridgeGrid.point K (Fin.last K)) e = if e ∈ B then 1 else 0
      rw [BridgeGrid.terminal K hK, physicalProbability_vertex]
      rfl
    by_cases he : e ∈ B
    · exact iff_of_true (hone _ e (by simpa [he] using heq)) he
    · exact iff_of_false (hzero _ e (by simpa [he] using heq)) he
  let level := ((3 : ℝ) / 4 - 2 / N) * V
  let good := fun C : Finset (Fin n) => level ≤ f.value (Q ∪ C)
  have hlevel : level ≤ V := by
    dsimp [level]
    have hdiv : (0 : ℝ) ≤ 2 / N := by positivity
    nlinarith [mul_nonneg hdiv hV.le]
  have hmono : ∀ C C', C ⊆ C' → good C → good C' := by
    intro C C' hCC hgood
    exact hgood.trans (f.monotone _ _ (Finset.union_subset_union_right hCC))
  have hinter (j : Fin K) : good (D ∪ (S j.castSucc ∩ S j.succ)) := by
    have hi := physical_intersection_lower f cores Q V hV.le hcoreV
      (BridgeGrid.point K j.castSucc) (BridgeGrid.point K j.succ)
      (BridgeGrid.simplex K hK _) (BridgeGrid.simplex K hK _)
    have htype := BridgeGrid.type_value f A B Q V hV.le hA hB K hK j.castSucc
    have hstep := mul_le_mul_of_nonneg_left (BridgeGrid.step K hK j) hV.le
    have hfrac : (2 : ℝ) / K = 1 / (N : ℝ) := by dsimp [K]; push_cast; field_simp
    rw [hfrac] at hstep
    have hlower := f.contractOn_expectation_add_forced_lower U D Q
      (fun e => min (z j.castSucc e) (z j.succ e)) (hmincube j)
      (fun e he => by simp only [hsupport _ e he, min_self])
    have hval := hvalues j
    have hsint : (S j.castSucc ∩ S j.succ) ∩ U = S j.castSucc ∩ S j.succ :=
      Finset.inter_eq_left.mpr (Finset.inter_subset_left.trans (hSU _))
    change finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) g.value - V / N ≤
      f.value ((D ∪ Q) ∪ ((S j.castSucc ∩ S j.succ) ∩ U)) - f.value (D ∪ Q) at hval
    rw [hsint] at hval
    have heq : Q ∪ (D ∪ (S j.castSucc ∩ S j.succ)) = (D ∪ Q) ∪ (S j.castSucc ∩ S j.succ) := by
      ext e; simp only [Finset.mem_union]; tauto
    change level ≤ f.value (Q ∪ (D ∪ (S j.castSucc ∩ S j.succ)))
    rw [heq]
    change _ ≤ finiteExpectation (fun e => min (z j.castSucc e) (z j.succ e)) _ at hi
    change finiteExpectation _ _ - f.value (D ∪ Q) ≤ finiteExpectation _ g.value at hlower
    change (3 : ℝ) / 4 * V ≤ finiteExpectation (BridgeGrid.point K j.castSucc)
      (f.onTypes cores Q).value at htype
    dsimp only [level]
    dsimp only [typeL1] at hstep
    simp only [div_eq_mul_inv] at hstep hval ⊢
    nlinarith only [htype, hi, hstep, hlower, hval]
  let C := ⌊(κ : ℝ) + (κ : ℝ) / N⌋₊
  have hSC (j) : (S j).card ≤ C := Nat.le_floor (hcards j)
  have hκC : κ ≤ C := Nat.le_floor (le_add_of_nonneg_right (by positivity))
  have hgood0 : good (D ∪ S 0) := by
    rw [hS0]
    exact hmono A _ Finset.subset_union_right (hlevel.trans hA)
  obtain ⟨P, hlen, hinit, hterm, hP⟩ := SetOperationPath.exists_chain_fin S C U
    (fun S => good (D ∪ S)) (fun C C' hCC hg => hmono _ _
      (Finset.union_subset_union_right hCC) hg) hgood0 (fun j => ⟨hSU j, hSC j⟩) hinter
  let R := P.withForced D
  have hR (j) : R.node j ⊆ U ∧ (R.node j).card ≤ C + H ∧ good (R.node j) := by
    exact ⟨Finset.union_subset hDU (hP j).1,
      (Finset.card_union_le _ _).trans (by have := (hP j).2.1; omega), (hP j).2.2⟩
  obtain ⟨L, hLlen, hLinit, hLterm, hL⟩ := R.prepend_forced A D U (C + H) good hmono
    (by change D ∪ P.node 0 = D ∪ A; rw [hinit, hS0]) (hlevel.trans hA)
    Finset.subset_union_left hDU (by omega) hR
  obtain ⟨T, hTlen, hTinit, hTterm, hT⟩ := L.append_unforced B D U (C + H) good hmono
    (by rw [hLterm]; change D ∪ P.node P.length = D ∪ B; rw [hterm, hS1])
    (hlevel.trans hB) Finset.subset_union_right hDU (by omega) hL
  refine ⟨T, hTinit.trans hLinit, hTterm, ?_, ?_⟩
  · have hplen : (P.length : ℝ) < 8 * κ := by
      rw [hlen, Nat.cast_sum]
      exact hcost
    have htlen : T.length = P.length + 2 * D.card := by
      rw [hTlen, hLlen]
      change D.card + P.length + D.card = P.length + 2 * D.card
      omega
    rw [htlen]
    have hplenn : P.length ≤ 8 * κ := by exact_mod_cast hplen.le
    omega
  · intro j
    refine ⟨(hT j).1, ?_, (hT j).2.2⟩
    have hh : ((T.node j).card : ℝ) ≤ (C + H : ℕ) := Nat.cast_le.mpr (hT j).2.1
    have hc : (C : ℝ) ≤ (κ : ℝ) + (κ : ℝ) / N := Nat.floor_le (by positivity)
    push_cast at hh
    dsimp [H] at hh
    linarith

/-- Uniform bridge with pure endpoints. Its operation bound is independent of
all instance sizes, and its additive cardinality overhead depends only on `N`. -/
theorem exists_rounded_bridge (A B Q : Finset (Fin n)) (N κ : ℕ) (V : ℝ)
    (hN : 0 < N) (hV : 0 ≤ V)
    (hAc : A.card ≤ κ) (hBc : B.card ≤ κ) (hAv : f.value A ≤ V) (hBv : f.value B ≤ V)
    (hA : V ≤ f.value (Q ∪ A)) (hB : V ≤ f.value (Q ∪ B)) :
    ∃ P : SetOperationPath n, P.node 0 = A ∧ P.node P.length = B ∧ P.length ≤ 10 * κ ∧
      ∀ j, P.node j ⊆ A ∪ B ∧ ((P.node j).card : ℝ) ≤ κ + (κ : ℝ) / N + bridgeHeavy N ∧
        ((3 : ℝ) / 4 - 2 / N) * V ≤ f.value (Q ∪ P.node j) := by
  by_cases hV0 : V = 0
  · obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_zero_bridge A B Q
    refine ⟨P, h0, h1, by omega, ?_⟩
    intro j
    refine ⟨(hnode j).1, ?_, ?_⟩
    · have hc : ((P.node j).card : ℝ) ≤ κ :=
        Nat.cast_le.mpr ((hnode j).2.1.trans (max_le hAc hBc))
      have hdiv : (0 : ℝ) ≤ (κ : ℝ) / N := by positivity
      have hH : (0 : ℝ) ≤ bridgeHeavy N := Nat.cast_nonneg _
      linarith
    · simpa [hV0] using (hnode j).2.2
  · by_cases hκ : bridgeHeavy N ≤ κ
    · exact f.exists_rounded_bridge_large A B Q N κ V hN hκ (lt_of_le_of_ne hV (Ne.symm hV0))
        hAc hBc hAv hBv hA hB
    · obtain ⟨P, h0, h1, hlen, hnode⟩ := f.exists_insertion_first_bridge A B Q V hA hB
      refine ⟨P, h0, h1, by omega, ?_⟩
      intro j
      refine ⟨(hnode j).1, ?_, ?_⟩
      · have hc : ((P.node j).card : ℝ) ≤ κ + bridgeHeavy N := by
          exact_mod_cast (show (P.node j).card ≤ κ + bridgeHeavy N by have := (hnode j).2.1; omega)
        have hdiv : (0 : ℝ) ≤ (κ : ℝ) / N := by positivity
        linarith
      · have hdiv : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
        have hh := mul_nonneg hdiv hV
        nlinarith [(hnode j).2.2]

end Objective
end ConsistentSubmodular
