module

public import ConsistentSubmodular.Deterministic.Certificates.Checkpoint

@[expose] public section

/-! Suffix reduction. Atoms whose retained incidence is empty receive zero
weight; their old mass is restored as baseline, never as covered mass. -/

noncomputable section
open scoped BigOperators
open Finset

namespace ConsistentSubmodular
namespace AtomicProfile

variable {m atomCount : ℕ}

def suffixIndex (h : Fin (m + 1)) (i : Fin (m - h.val + 1)) : Fin (m + 1) :=
  ⟨h.val + i.val, by have := h.isLt; have := i.isLt; omega⟩

def suffixInverse (h i : Fin (m + 1)) (hi : h ≤ i) : Fin (m - h.val + 1) :=
  ⟨i.val - h.val, by have := i.isLt; have := h.isLt; omega⟩

@[simp] theorem suffixIndex_val (h : Fin (m + 1)) (i : Fin (m - h.val + 1)) :
    (suffixIndex h i).val = h.val + i.val := rfl

@[simp] theorem suffixIndex_zero (h : Fin (m + 1)) : suffixIndex h 0 = h := by
  apply Fin.ext; simp [suffixIndex]

@[simp] theorem suffixIndex_last (h : Fin (m + 1)) :
    suffixIndex h (Fin.last (m - h.val)) = Fin.last m := by
  apply Fin.ext
  have := h.isLt
  simp only [suffixIndex_val, Fin.val_last]
  omega

theorem suffixIndex_injective (h : Fin (m + 1)) : Function.Injective (suffixIndex h) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simpa only [suffixIndex_val, Nat.add_left_cancel_iff] using this

@[simp] theorem suffixIndex_inverse (h i : Fin (m + 1)) (hi : h ≤ i) :
    suffixIndex h (suffixInverse h i hi) = i := by
  apply Fin.ext
  dsimp [suffixIndex, suffixInverse]
  have : h.val ≤ i.val := hi
  omega

@[simp] theorem suffixInverse_index (h : Fin (m + 1)) (i : Fin (m - h.val + 1))
    (hi : h ≤ suffixIndex h i) : suffixInverse h (suffixIndex h i) hi = i := by
  apply Fin.ext
  simp [suffixInverse, suffixIndex]

def retainedLabels (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (a : Fin atomCount) : Finset (Fin (m - h.val + 1)) :=
  univ.filter (fun i => suffixIndex h i ∈ P.labels a)

@[simp] theorem mem_retainedLabels (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (a : Fin atomCount) (i : Fin (m - h.val + 1)) :
    i ∈ P.retainedLabels h a ↔ suffixIndex h i ∈ P.labels a := by
  simp [retainedLabels]

theorem pool_ge_of_retained (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (a : Fin atomCount) (ha : (P.retainedLabels h a).Nonempty) : h ≤ P.pool a := by
  obtain ⟨i, hi⟩ := ha
  have htri := P.triangular a _ ((P.mem_retainedLabels h a i).mp hi)
  have hlow : h ≤ suffixIndex h i := by change h.val ≤ h.val + i.val; omega
  exact hlow.trans htri

def suffixPool (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (a : Fin atomCount) : Fin (m - h.val + 1) :=
  ⟨(P.pool a).val - h.val, by have := (P.pool a).isLt; have := h.isLt; omega⟩

theorem suffixPool_le_iff (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (a : Fin atomCount) (ha : (P.retainedLabels h a).Nonempty)
    (t : Fin (m - h.val + 1)) : t ≤ P.suffixPool h a ↔ suffixIndex h t ≤ P.pool a := by
  have hpool : h.val ≤ (P.pool a).val := P.pool_ge_of_retained h a ha
  change t.val ≤ (P.pool a).val - h.val ↔ h.val + t.val ≤ (P.pool a).val
  omega

def suffix (P : AtomicProfile m atomCount) (h : Fin (m + 1)) :
    AtomicProfile (m - h.val) atomCount where
  pool := P.suffixPool h
  labels := fun a => if (P.retainedLabels h a).Nonempty then P.retainedLabels h a else {0}
  weight := fun a => if (P.retainedLabels h a).Nonempty then P.weight a else 0
  weight_nonnegative := by intro a; split_ifs; exact P.weight_nonnegative a; rfl
  labels_nonempty := by intro a; split_ifs with ha; exact ha; simp
  triangular := by
    intro a i hi
    by_cases ha : (P.retainedLabels h a).Nonempty
    · simp only [ha, if_pos, mem_retainedLabels] at hi
      apply (P.suffixPool_le_iff h a ha i).mpr
      exact P.triangular a _ hi
    · simp only [ha, if_false, mem_singleton] at hi
      rw [hi]
      exact Fin.zero_le _
  terminal := by
    intro a hw hp
    have ha : (P.retainedLabels h a).Nonempty := by
      by_contra ha
      simp [ha] at hw
    have hpool : h.val ≤ (P.pool a).val := P.pool_ge_of_retained h a ha
    have heq : P.pool a = Fin.last m := by
      apply Fin.ext
      have heq := congrArg Fin.val hp
      dsimp [suffixPool] at heq
      simp only [Fin.val_last]
      have := h.isLt
      omega
    have hw' : 0 < P.weight a := by simpa [ha] using hw
    simp only [ha, if_pos, mem_retainedLabels, suffixIndex_last]
    exact P.terminal a hw' heq

theorem suffix_residual (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (i t : Fin (m - h.val + 1)) :
    (P.suffix h).residual i t = P.residual (suffixIndex h i) (suffixIndex h t) := by
  unfold residual
  apply sum_congr rfl
  intro a _
  by_cases ha : (P.retainedLabels h a).Nonempty
  · simp only [suffix, ha, if_pos, mem_retainedLabels,
      P.suffixPool_le_iff h a ha t]
  · have hi : suffixIndex h i ∉ P.labels a := by
      intro hi
      exact ha ⟨i, (P.mem_retainedLabels h a i).mpr hi⟩
    simp [suffix, ha, hi]

@[simp] theorem suffix_designated (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (t : Fin (m - h.val + 1)) :
    (P.suffix h).designated t = P.designated (suffixIndex h t) :=
  P.suffix_residual h t t

theorem suffix_canonical (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hh : P.designated h = 1) : (P.suffix h).Canonical := by
  constructor
  · simpa using hh
  · intro t i
    rw [P.suffix_residual, P.suffix_designated]
    exact hP.2 _ _

theorem suffix_strict (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hlast : ∀ i, h < i → P.designated i ≠ 1)
    (t : Fin (m - h.val + 1)) (ht : 0 < t) : (P.suffix h).designated t < 1 := by
  rw [P.suffix_designated]
  apply lt_of_le_of_ne (P.designated_le_one hP _)
  apply hlast
  change h.val < h.val + t.val
  have : 0 < t.val := ht
  omega

theorem suffix_baseline_le (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (t : Fin (m - h.val + 1)) : (P.suffix h).baseline t ≤ P.baseline (suffixIndex h t) := by
  unfold baseline
  apply sum_le_sum
  intro a _
  by_cases ha : (P.retainedLabels h a).Nonempty
  · have heq : P.suffixPool h a < t ↔ P.pool a < suffixIndex h t := by
      rw [← not_le, ← not_le, P.suffixPool_le_iff h a ha t]
    simp only [suffix, ha, if_pos, heq]
    exact le_rfl
  · simp only [suffix, ha, if_false]
    split_ifs <;> linarith [P.weight_nonnegative a]

def restoredBaseline (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (t : Fin (m - h.val + 1)) : ℝ := P.baseline (suffixIndex h t) - (P.suffix h).baseline t

theorem restoredBaseline_nonnegative (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (t : Fin (m - h.val + 1)) : 0 ≤ P.restoredBaseline h t :=
  sub_nonneg.mpr (P.suffix_baseline_le h t)

theorem suffix_benchmark_identity (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (t : Fin (m - h.val + 1)) :
    P.benchmark (suffixIndex h t) = (P.suffix h).benchmark t + P.restoredBaseline h t := by
  unfold benchmark restoredBaseline
  rw [P.suffix_designated]
  ring

def suffixLift (h : Fin (m + 1)) (p : Point (m - h.val)) : Point m :=
  fun i => if hi : h ≤ i then p (suffixInverse h i hi) else 0

@[simp] theorem suffixLift_index (h : Fin (m + 1)) (p : Point (m - h.val))
    (i : Fin (m - h.val + 1)) : suffixLift h p (suffixIndex h i) = p i := by
  have hi : h ≤ suffixIndex h i := by change h.val ≤ h.val + i.val; omega
  simp [suffixLift, hi]

theorem prod_suffixLift (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (a : Fin atomCount) :
    (∏ i ∈ P.labels a, (1 - suffixLift h p i)) =
      ∏ i ∈ P.retainedLabels h a, (1 - p i) := by
  have hf : (∏ i ∈ (P.labels a).filter (fun i => h ≤ i), (1 - suffixLift h p i)) =
      ∏ i ∈ P.labels a, (1 - suffixLift h p i) := by
    apply prod_filter_of_ne
    intro i hi hne
    by_contra hn
    exact hne (by simp [suffixLift, hn])
  rw [← hf]
  symm
  apply prod_bij (fun i _ => suffixIndex h i)
  · intro i hi
    exact mem_filter.mpr ⟨(P.mem_retainedLabels h a i).mp hi,
      by change h.val ≤ h.val + i.val; omega⟩
  · intro i hi j hj hij
    exact suffixIndex_injective h hij
  · intro i hi
    have hh := (mem_filter.mp hi).2
    refine ⟨suffixInverse h i hh, ?_, suffixIndex_inverse h i hh⟩
    simp only [mem_retainedLabels, suffixIndex_inverse]
    exact (mem_filter.mp hi).1
  · intro i hi
    simp

theorem discarded_product (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (a : Fin atomCount)
    (ha : ¬ (P.retainedLabels h a).Nonempty) :
    (∏ i ∈ P.labels a, (1 - suffixLift h p i)) = 1 := by
  rw [P.prod_suffixLift]
  have he : P.retainedLabels h a = ∅ := not_nonempty_iff_eq_empty.mp ha
  simp [he]

theorem suffix_value_identity (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (t : Fin (m - h.val + 1)) :
    P.value (suffixIndex h t) (suffixLift h p) =
      (P.suffix h).value t p + P.restoredBaseline h t := by
  have hs : (∑ a, if suffixIndex h t ≤ P.pool a then
      P.weight a * (1 - ∏ i ∈ P.labels a, (1 - suffixLift h p i)) else 0) =
      ∑ a, if t ≤ (P.suffix h).pool a then
      (P.suffix h).weight a * (1 - ∏ i ∈ (P.suffix h).labels a, (1 - p i)) else 0 := by
    apply sum_congr rfl
    intro a _
    by_cases ha : (P.retainedLabels h a).Nonempty
    · rw [P.prod_suffixLift]
      simp only [suffix, ha, if_pos, P.suffixPool_le_iff h a ha t]
    · rw [P.discarded_product h p a ha]
      simp [suffix, ha]
  unfold value restoredBaseline
  rw [hs]
  ring

theorem suffix_margin_identity (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (t : Fin (m - h.val + 1)) :
    P.value (suffixIndex h t) (suffixLift h p) - (3 : ℝ) / 4 * P.benchmark (suffixIndex h t) =
      (P.suffix h).value t p - (3 : ℝ) / 4 * (P.suffix h).benchmark t +
        P.restoredBaseline h t / 4 := by
  rw [P.suffix_value_identity, P.suffix_benchmark_identity]
  ring

theorem suffix_early_value (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (t : Fin (m + 1)) (ht : t ≤ h) :
    P.value t (suffixLift h p) = P.baseline t + (P.suffix h).value 0 p := by
  have hs : (∑ a, if t ≤ P.pool a then
      P.weight a * (1 - ∏ i ∈ P.labels a, (1 - suffixLift h p i)) else 0) =
      ∑ a, if (0 : Fin (m - h.val + 1)) ≤ (P.suffix h).pool a then
      (P.suffix h).weight a * (1 - ∏ i ∈ (P.suffix h).labels a, (1 - p i)) else 0 := by
    apply sum_congr rfl
    intro a _
    by_cases ha : (P.retainedLabels h a).Nonempty
    · have hpool := ht.trans (P.pool_ge_of_retained h a ha)
      rw [P.prod_suffixLift]
      simp only [suffix, ha, if_pos, hpool, Fin.zero_le]
    · rw [P.discarded_product h p a ha]
      simp [suffix, ha]
  unfold value
  rw [hs, baseline_zero]
  ring

theorem suffix_early_designated (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hh : P.designated h = 1) (t : Fin (m + 1)) (ht : t ≤ h) :
    P.designated t = 1 := by
  have h1 := P.designated_antitone hP ht
  have h2 := P.designated_le_one hP t
  linarith

@[simp] theorem suffix_initial_value (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) : P.value 0 (suffixLift h p) = (P.suffix h).value 0 p := by
  rw [P.suffix_early_value h p 0 (Fin.zero_le _), P.baseline_zero, zero_add]

theorem suffix_early_margin (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hh : P.designated h = 1) (p : Point (m - h.val))
    (t : Fin (m + 1)) (ht : t ≤ h) :
    P.value t (suffixLift h p) - (3 : ℝ) / 4 * P.benchmark t =
      (P.suffix h).value 0 p - (3 : ℝ) / 4 + P.baseline t / 4 := by
  rw [P.suffix_early_value h p t ht]
  unfold benchmark
  rw [P.suffix_early_designated hP h hh t ht]
  ring

theorem suffixLift_sum (h : Fin (m + 1)) (p : Point (m - h.val)) :
    (∑ i, suffixLift h p i) = ∑ i, p i := by
  have hf : (∑ i ∈ univ.filter (fun i : Fin (m + 1) => h ≤ i), suffixLift h p i) =
      ∑ i, suffixLift h p i := by
    apply sum_filter_of_ne
    intro i _ hne
    by_contra hn
    exact hne (by simp [suffixLift, hn])
  rw [← hf]
  symm
  apply sum_bij (fun i _ => suffixIndex h i)
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, by change h.val ≤ h.val + i.val; omega⟩
  · intro i hi j hj hij
    exact suffixIndex_injective h hij
  · intro i hi
    have hh := (mem_filter.mp hi).2
    exact ⟨suffixInverse h i hh, mem_univ _, suffixIndex_inverse h i hh⟩
  · intro i hi
    simp

theorem suffixLift_simplex (h : Fin (m + 1)) {p : Point (m - h.val)}
    (hp : IsSimplex p) : IsSimplex (suffixLift h p) := by
  constructor
  · intro i
    unfold suffixLift
    split_ifs
    · exact hp.1 _
    · exact le_rfl
  · rw [suffixLift_sum]
    exact hp.2

@[simp] theorem suffixLift_mix (h : Fin (m + 1)) (p q : Point (m - h.val)) (x : ℝ) :
    suffixLift h (mix p q x) = mix (suffixLift h p) (suffixLift h q) x := by
  funext i
  by_cases hi : h ≤ i <;> simp [suffixLift, mix, hi]

@[simp] theorem suffixLift_vertex (h : Fin (m + 1)) (i : Fin (m - h.val + 1)) :
    suffixLift h (vertex i) = vertex (suffixIndex h i) := by
  funext j
  by_cases hj : h ≤ j
  · have heq : suffixInverse h j hj = i ↔ j = suffixIndex h i := by
      constructor
      · intro heq
        rw [← heq, suffixIndex_inverse]
      · intro heq
        subst j
        exact suffixInverse_index h i hj
    simp [suffixLift, hj, vertex, heq]
  · have hne : j ≠ suffixIndex h i := by
      intro heq
      apply hj
      rw [heq]
      change h.val ≤ h.val + i.val
      omega
    simp [suffixLift, hj, vertex, hne]

theorem suffixLift_support (h : Fin (m + 1)) (p : Point (m - h.val)) :
    supportCard (suffixLift h p) = supportCard p := by
  have heq : univ.filter (fun i => suffixLift h p i ≠ 0) =
      (univ.filter (fun i => p i ≠ 0)).image (suffixIndex h) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hj
      have hh : h ≤ j := by
        by_contra hh
        exact hj (by simp [suffixLift, hh])
      refine ⟨suffixInverse h j hh, ?_, suffixIndex_inverse h j hh⟩
      simpa [suffixLift, hh] using hj
    · rintro ⟨i, hi, rfl⟩
      simpa using hi
  unfold supportCard
  rw [heq, card_image_of_injective _ (suffixIndex_injective h)]

theorem suffix_stage_safe (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (p : Point (m - h.val)) (t : Fin (m - h.val + 1))
    (ht : (3 : ℝ) / 4 * (P.suffix h).benchmark t ≤ (P.suffix h).value t p) :
    (3 : ℝ) / 4 * P.benchmark (suffixIndex h t) ≤
      P.value (suffixIndex h t) (suffixLift h p) := by
  have heq := P.suffix_margin_identity h p t
  have hn := P.restoredBaseline_nonnegative h t
  linarith

def suffixPath (h : Fin (m + 1)) (γ : PolygonalPath (m - h.val)) : PolygonalPath m where
  pieces := γ.pieces
  node := fun i => suffixLift h (γ.node i)

theorem suffixPath_initial_safe (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (γ : PolygonalPath (m - h.val)) (hγ : SafePath (P.suffix h) 0 ((3 : ℝ) / 4) γ) :
    SafePath P 0 ((3 : ℝ) / 4) (suffixPath h γ) := by
  constructor
  · intro i
    refine ⟨suffixLift_simplex h (hγ.1 i).1, ?_⟩
    change (3 : ℝ) / 4 ≤ P.value 0 (suffixLift h (γ.node i))
    rw [P.suffix_initial_value]
    exact (hγ.1 i).2
  · intro j x hx hx1
    change IsSimplex (mix (suffixLift h (γ.node j.castSucc)) (suffixLift h (γ.node j.succ)) x) ∧ _
    rw [← suffixLift_mix]
    refine ⟨suffixLift_simplex h (hγ.2 j x hx hx1).1, ?_⟩
    change (3 : ℝ) / 4 ≤ P.value 0 (mix (suffixLift h (γ.node j.castSucc)) (suffixLift h (γ.node j.succ)) x)
    rw [← suffixLift_mix, P.suffix_initial_value]
    exact (hγ.2 j x hx hx1).2

theorem suffixPath_terminal_safe (P : AtomicProfile m atomCount) (h : Fin (m + 1))
    (γ : PolygonalPath (m - h.val))
    (hγ : SafePath (P.suffix h) (Fin.last (m - h.val))
      ((3 : ℝ) / 4 * (P.suffix h).benchmark (Fin.last (m - h.val))) γ) :
    SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) (suffixPath h γ) := by
  constructor
  · intro i
    refine ⟨suffixLift_simplex h (hγ.1 i).1, ?_⟩
    have hg := P.suffix_stage_safe h (γ.node i) (Fin.last (m - h.val)) (hγ.1 i).2
    simpa only [suffixIndex_last] using hg
  · intro j x hx hx1
    change IsSimplex (mix (suffixLift h (γ.node j.castSucc)) (suffixLift h (γ.node j.succ)) x) ∧ _
    rw [← suffixLift_mix]
    refine ⟨suffixLift_simplex h (hγ.2 j x hx hx1).1, ?_⟩
    have hg := P.suffix_stage_safe h _ (Fin.last (m - h.val)) (hγ.2 j x hx hx1).2
    simpa only [suffixIndex_last, suffixLift_mix, suffixPath] using hg

def plateauBridge (h : Fin (m + 1)) : PolygonalPath m :=
  if h = 0 then PolygonalPath.constant (vertex 0) else PolygonalPath.segment (vertex 0) (vertex h)

@[simp] theorem plateauBridge_initial (h : Fin (m + 1)) : (plateauBridge h).node 0 = vertex 0 := by
  by_cases hh : h = 0
  · subst h; rfl
  · exact (congrArg (fun γ : PolygonalPath m => γ.node 0)
      (show plateauBridge h = PolygonalPath.segment (vertex 0) (vertex h) from if_neg hh)).trans
      (PolygonalPath.segment_initial _ _)

@[simp] theorem plateauBridge_terminal (h : Fin (m + 1)) :
    (plateauBridge h).node (Fin.last (plateauBridge h).pieces) = vertex h := by
  by_cases hh : h = 0
  · subst h; rfl
  · exact (congrArg (fun γ : PolygonalPath m => γ.node (Fin.last γ.pieces))
      (show plateauBridge h = PolygonalPath.segment (vertex 0) (vertex h) from if_neg hh)).trans
      (PolygonalPath.segment_terminal _ _)

theorem plateauBridge_pieces (h : Fin (m + 1)) : (plateauBridge h).pieces ≤ h.val := by
  by_cases hh : h = 0
  · simp [plateauBridge, hh]
  · simp only [plateauBridge, hh, if_false, PolygonalPath.segment_pieces]
    have hn : h.val ≠ 0 := fun hz => hh (Fin.ext hz)
    omega

theorem plateauBridge_safe (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hh : P.designated h = 1) :
    SafePath P 0 ((3 : ℝ) / 4) (plateauBridge h) := by
  by_cases hz : h = 0
  · simp only [plateauBridge, hz, if_true]
    apply (safePath_constant_iff _ _ _ _).mpr
    refine ⟨simplex_vertex _, ?_⟩
    rw [P.value_designated_vertex, P.benchmark_zero hP]
    norm_num
  · simp only [plateauBridge, hz, if_false]
    apply safePath_segment
    intro x hx hx1
    refine ⟨(simplex_vertex 0).mix (simplex_vertex h) hx hx1, ?_⟩
    have hO : P.overlap 0 h 0 ≤ 1 := by
      have ho := P.overlap_le_left 0 h 0
      change P.overlap 0 h 0 ≤ P.designated 0 at ho
      rwa [hP.1] at ho
    have hg := P.value_mix_vertices_sufficient 0 0 h (Ne.symm hz) hx hx1 hO
    rw [P.baseline_zero, P.residual_persistence _ _ (Fin.zero_le _),
      P.residual_persistence _ _ (Fin.zero_le _), hP.1, hh] at hg
    linarith

/-- Lift a complete suffix certificate with the exact same checkpoint on entry
and exit. The discarded mass can only improve all stage margins. -/
def liftSuffixCheckpoint (P : AtomicProfile m atomCount) (hP : P.Canonical)
    (h : Fin (m + 1)) (hh : P.designated h = 1)
    (c : CheckpointCertificate (P.suffix h)) : CheckpointCertificate P := by
  let en := suffixPath h c.entry
  let ex := suffixPath h c.exit
  have hjoin : (plateauBridge h).node (Fin.last (plateauBridge h).pieces) = en.node 0 := by
    change _ = suffixLift h (c.entry.node 0)
    rw [plateauBridge_terminal, c.entry_initial, suffixLift_vertex, suffixIndex_zero]
  have hend : en.node (Fin.last en.pieces) = suffixLift h c.point := by
    change suffixLift h (c.entry.node (Fin.last c.entry.pieces)) = _
    rw [c.entry_terminal]
  refine {
    point := suffixLift h c.point
    entry := PolygonalPath.append (plateauBridge h) en
    exit := ex
    simplex := suffixLift_simplex h c.simplex
    support := by rw [suffixLift_support]; exact c.support
    stages := ?_
    entry_initial := by rw [PolygonalPath.append_initial, plateauBridge_initial]
    entry_terminal := by rw [PolygonalPath.append_terminal _ _ hjoin, hend]
    exit_initial := ?_
    exit_terminal := ?_
    entry_safe := (P.plateauBridge_safe hP h hh).append
      (P.suffixPath_initial_safe h c.entry c.entry_safe) hjoin
    exit_safe := P.suffixPath_terminal_safe h c.exit c.exit_safe
    piece_budget := ?_ }
  · intro t
    by_cases ht : t ≤ h
    · have hm := P.suffix_early_margin hP h hh c.point t ht
      have hg := c.stages 0
      rw [(P.suffix h).benchmark_zero (P.suffix_canonical hP h hh)] at hg
      have hb := P.baseline_nonnegative t
      linarith
    · have hh' : h ≤ t := le_of_lt (lt_of_not_ge ht)
      have hg := P.suffix_stage_safe h c.point (suffixInverse h t hh') (c.stages _)
      simpa only [suffixIndex_inverse] using hg
  · change suffixLift h (c.exit.node 0) = suffixLift h c.point
    rw [c.exit_initial]
  · change suffixLift h (c.exit.node (Fin.last c.exit.pieces)) = vertex (Fin.last m)
    rw [c.exit_terminal, suffixLift_vertex, suffixIndex_last]
  · change (plateauBridge h).pieces + c.entry.pieces + c.exit.pieces ≤ (m + 1) + 2
    have hb := plateauBridge_pieces h
    have hc := c.piece_budget
    have hh := h.isLt
    omega

theorem exists_last_unit (P : AtomicProfile m atomCount) (hP : P.Canonical) :
    ∃ h : Fin (m + 1), P.designated h = 1 ∧ ∀ i, h < i → P.designated i ≠ 1 := by
  let units := univ.filter (fun i => P.designated i = 1)
  have hn : units.Nonempty := ⟨0, mem_filter.mpr ⟨mem_univ _, hP.1⟩⟩
  let h := units.max' hn
  refine ⟨h, (mem_filter.mp (max'_mem units hn)).2, ?_⟩
  intro i hi heq
  have hmem : i ∈ units := mem_filter.mpr ⟨mem_univ _, heq⟩
  have hle : i ≤ h := le_max' units i hmem
  exact (not_le.mpr hi) hle

end AtomicProfile

/-- It suffices to solve the normalized case whose designated residual is
strictly below one at every positive stage. This reduction includes the deletion
of empty incidences and the complete path piece budget. -/
theorem finiteCheckpoint_of_strict
    (strict : ∀ m a : ℕ, ∀ P : AtomicProfile m a, P.Canonical →
      (∀ t : Fin (m + 1), 0 < t → P.designated t < 1) →
      Nonempty (CheckpointCertificate P)) : FiniteCheckpointGoal := by
  rw [finiteCheckpointGoal_iff]
  intro m a P hP
  obtain ⟨h, hh, hlast⟩ := P.exists_last_unit hP
  obtain ⟨c⟩ := strict (m - h.val) a (P.suffix h) (P.suffix_canonical hP h hh)
    (P.suffix_strict hP h hlast)
  exact ⟨P.liftSuffixCheckpoint hP h hh c⟩

end ConsistentSubmodular
