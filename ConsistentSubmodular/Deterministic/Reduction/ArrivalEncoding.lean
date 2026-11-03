module

public import ConsistentSubmodular.Deterministic.Basic.Paths

@[expose] public section

/-!
# Single-arrival windows suffice

The windows of Section 3.2 add one arrival per stage, while the reduction of
Theorem 5 needs certificates for compressed windows whose stages add several
arrivals. A window with arbitrary nested arrivals is encoded as a
single-arrival window on a larger ground set: the new element of stage `j + 1`
stands for all arrivals up to that stage. The encoding has the same stages,
candidates, benchmarks, and mixture values, so a certificate of the encoding
is a certificate of the original window.
-/

noncomputable section
open scoped BigOperators
namespace ConsistentSubmodular
namespace WindowInstance

variable {n : ℕ} (W : WindowInstance n)

/-- Elements of the encoding's ground set read as sets of original elements:
an old element stands for itself and the new element of stage `j + 1` for the
arrivals `R_{j+1}`. -/
def decode (X : Finset (Fin (n + W.lastStage))) : Finset (Fin n) :=
  Finset.univ.filter (fun e => Fin.castAdd W.lastStage e ∈ X) ∪
    (Finset.univ.filter (fun j : Fin W.lastStage => Fin.natAdd n j ∈ X)).biUnion
      (fun j => W.arrivals j.succ)

theorem mem_decode (X : Finset (Fin (n + W.lastStage))) (e : Fin n) :
    e ∈ W.decode X ↔ Fin.castAdd W.lastStage e ∈ X ∨
      ∃ j : Fin W.lastStage, Fin.natAdd n j ∈ X ∧ e ∈ W.arrivals j.succ := by
  simp [decode]

theorem decode_empty : W.decode ∅ = ∅ := by
  ext e
  simp [mem_decode]

theorem decode_union (X Y : Finset (Fin (n + W.lastStage))) :
    W.decode (X ∪ Y) = W.decode X ∪ W.decode Y := by
  ext e
  simp only [mem_decode, Finset.mem_union]
  constructor
  · rintro ((h | h) | ⟨j, hj | hj, he⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨j, hj, he⟩)
    · exact Or.inr (Or.inr ⟨j, hj, he⟩)
  · rintro ((h | ⟨j, hj, he⟩) | (h | ⟨j, hj, he⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨j, Or.inl hj, he⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨j, Or.inr hj, he⟩

theorem decode_mono {X Y : Finset (Fin (n + W.lastStage))} (h : X ⊆ Y) :
    W.decode X ⊆ W.decode Y := by
  intro e he
  rw [mem_decode] at he ⊢
  rcases he with he | ⟨j, hj, he⟩
  · exact Or.inl (h he)
  · exact Or.inr ⟨j, h hj, he⟩

theorem decode_biUnion {d : ℕ} (I : Finset (Fin d))
    (F : Fin d → Finset (Fin (n + W.lastStage))) :
    W.decode (I.biUnion F) = I.biUnion (fun i => W.decode (F i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp [decode_empty]
  | @insert a I _ ih => rw [Finset.biUnion_insert, Finset.biUnion_insert, decode_union, ih]

/-- The objective of the encoding. -/
def encodedObjective : Objective (n + W.lastStage) where
  value X := W.objective.value (W.decode X)
  nonnegative X := W.objective.nonnegative _
  monotone X Y h := W.objective.monotone _ _ (W.decode_mono h)
  submodular X Y := by
    rw [W.decode_union]
    have hs := W.objective.submodular (W.decode X) (W.decode Y)
    have hm := W.objective.monotone _ _ (Finset.subset_inter
      (W.decode_mono (Finset.inter_subset_left : X ∩ Y ⊆ X))
      (W.decode_mono (Finset.inter_subset_right : X ∩ Y ⊆ Y)))
    linarith

/-- The arrivals of the encoding: the new elements of the first `j` stages. -/
def encodedArrivals (j : Fin (W.lastStage + 1)) : Finset (Fin (n + W.lastStage)) :=
  (Finset.univ.filter (fun i : Fin W.lastStage => i.val < j.val)).map (Fin.natAddEmb n)

theorem decode_embed (A : Finset (Fin n)) :
    W.decode (A.map (Fin.castAddEmb W.lastStage)) = A := by
  ext e
  rw [mem_decode]
  constructor
  · rintro (h | ⟨j, hj, -⟩)
    · obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp h
      have : a = e := Fin.castAdd_injective _ _ hae
      exact this ▸ ha
    · obtain ⟨a, -, hae⟩ := Finset.mem_map.mp hj
      have hv := congrArg Fin.val hae
      simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
      have := a.isLt
      omega
  · intro he
    exact Or.inl (Finset.mem_map_of_mem _ he)

theorem decode_encodedArrivals (j : Fin (W.lastStage + 1)) :
    W.decode (W.encodedArrivals j) = W.arrivals j := by
  ext e
  rw [mem_decode]
  simp only [encodedArrivals, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.natAddEmb_apply]
  constructor
  · rintro (⟨a, -, hae⟩ | ⟨i, ⟨a, ha, hai⟩, he⟩)
    · have hv := congrArg Fin.val hae
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have := e.isLt
      omega
    · have hai' : a = i := Fin.natAdd_injective _ _ hai
      subst hai'
      exact W.arrivals_mono (show a.succ ≤ j from Fin.le_iff_val_le_val.mpr (by
        simp only [Fin.val_succ]; omega)) he
  · intro he
    right
    have hj : j ≠ 0 := by
      rintro rfl
      rw [W.arrivals_zero] at he
      exact Finset.notMem_empty e he
    have hj1 : 1 ≤ j.val := Nat.one_le_iff_ne_zero.mpr (fun h => hj (Fin.ext h))
    let i : Fin W.lastStage := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hij : i.succ = j := by
      apply Fin.ext
      simp only [i, Fin.val_succ]
      omega
    exact ⟨i, ⟨i, by simp only [i]; omega, rfl⟩, hij ▸ he⟩

theorem decode_subset_present {X : Finset (Fin (n + W.lastStage))}
    (hX : X ⊆ W.present.map (Fin.castAddEmb W.lastStage)) :
    W.decode X ⊆ W.present ∧ (W.decode X).card ≤ X.card := by
  have hdec : W.decode X = X.preimage (Fin.castAdd W.lastStage)
      (Fin.castAdd_injective _ _).injOn := by
    ext e
    rw [mem_decode, Finset.mem_preimage]
    constructor
    · rintro (h | ⟨j, hj, -⟩)
      · exact h
      · obtain ⟨a, -, hae⟩ := Finset.mem_map.mp (hX hj)
        have hv := congrArg Fin.val hae
        simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
        have := a.isLt
        omega
    · exact Or.inl
  rw [hdec]
  refine ⟨?_, ?_⟩
  · intro e he
    rw [Finset.mem_preimage] at he
    obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp (hX he)
    have : a = e := Fin.castAdd_injective _ _ hae
    exact this ▸ ha
  · apply Finset.card_le_card_of_injOn (Fin.castAdd W.lastStage)
    · intro e he
      exact Finset.mem_preimage.mp he
    · intro a _ b _ hab
      exact Fin.castAdd_injective _ _ hab

theorem decode_window_union (j : Fin (W.lastStage + 1)) (X : Finset (Fin (n + W.lastStage))) :
    W.decode (X ∪ W.encodedArrivals j) = W.decode X ∪ W.arrivals j := by
  rw [decode_union, decode_encodedArrivals]

/-- The single-arrival encoding of a window. -/
def encode : WindowInstance (n + W.lastStage) where
  objective := W.encodedObjective
  present := W.present.map (Fin.castAddEmb W.lastStage)
  coreBudget := W.coreBudget
  lastStage := W.lastStage
  arrivals := W.encodedArrivals
  candidate j := (W.candidate j).map (Fin.castAddEmb W.lastStage)
  arrivals_zero := by
    ext x
    simp [encodedArrivals]
  arrivals_mono := by
    intro i j hij x hx
    simp only [encodedArrivals, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx ⊢
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, lt_of_lt_of_le ha (Fin.le_iff_val_le_val.mp hij), hax⟩
  arrivals_disjoint := by
    intro j
    rw [Finset.disjoint_left]
    intro x hx hxp
    simp only [encodedArrivals, Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
      true_and, Fin.natAddEmb_apply] at hx
    obtain ⟨a, -, hax⟩ := hx
    obtain ⟨e, -, hex⟩ := Finset.mem_map.mp hxp
    have hv := congrArg Fin.val (hax.trans hex.symm)
    simp only [Fin.castAddEmb_apply, Fin.val_castAdd, Fin.val_natAdd] at hv
    have := e.isLt
    omega
  candidate_subset j := Finset.map_subset_map.mpr (W.candidate_subset j)
  candidate_card j := by
    rw [Finset.card_map]
    exact W.candidate_card j
  candidate_optimal j X hX hk := by
    change W.objective.value (W.decode (X ∪ W.encodedArrivals j)) ≤
      W.objective.value (W.decode ((W.candidate j).map (Fin.castAddEmb W.lastStage) ∪
        W.encodedArrivals j))
    rw [W.decode_window_union, W.decode_window_union, W.decode_embed]
    obtain ⟨hsub, hcard⟩ := W.decode_subset_present hX
    exact W.candidate_optimal j _ hsub (hcard.trans hk)

theorem natAdd_notMem_encodedArrivals (j : Fin W.lastStage) :
    Fin.natAdd n j ∉ W.encodedArrivals j.castSucc := by
  intro hx
  simp only [encodedArrivals, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.natAddEmb_apply, Fin.val_castSucc] at hx
  obtain ⟨a, ha, hax⟩ := hx
  have hv := congrArg Fin.val hax
  simp only [Fin.val_natAdd] at hv
  omega

theorem encodedArrivals_succ (j : Fin W.lastStage) :
    W.encodedArrivals j.succ = insert (Fin.natAdd n j) (W.encodedArrivals j.castSucc) := by
  ext x
  simp only [encodedArrivals, Finset.mem_insert, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.natAddEmb_apply, Fin.val_succ, Fin.val_castSucc]
  constructor
  · rintro ⟨a, ha, hax⟩
    by_cases haj : a.val = j.val
    · left
      rw [← hax, show a = j from Fin.ext haj]
    · right
      exact ⟨a, by omega, hax⟩
  · rintro (hx | ⟨a, ha, hax⟩)
    · exact ⟨j, by omega, hx.symm⟩
    · exact ⟨a, by omega, hax⟩

theorem encode_singleArrivals : W.encode.SingleArrivals :=
  fun j => ⟨Fin.natAdd n j, W.natAdd_notMem_encodedArrivals j, W.encodedArrivals_succ j⟩

theorem encode_benchmark (j : Fin (W.lastStage + 1)) : W.encode.benchmark j = W.benchmark j := by
  change W.objective.value (W.decode ((W.candidate j).map (Fin.castAddEmb W.lastStage) ∪
    W.encodedArrivals j)) = _
  rw [W.decode_window_union, W.decode_embed]
  rfl

theorem encode_mixtureValue (j : Fin (W.lastStage + 1)) (p : Point W.lastStage) :
    W.encode.mixtureValue j p = W.mixtureValue j p := by
  unfold mixtureValue
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  change W.objective.value (W.decode (W.encodedArrivals j ∪
    I.biUnion (fun i => (W.candidate i).map (Fin.castAddEmb W.lastStage)))) = _
  rw [decode_union, decode_encodedArrivals, decode_biUnion]
  simp only [decode_embed]
  rfl

namespace Certificate

variable {W}

/-- A certificate of the encoding is a certificate of the original window. -/
def ofEncode {α : ℝ} {L : ℕ} (Z : W.encode.Certificate α L) : W.Certificate α L where
  anchor := Z.anchor
  entry := Z.entry
  exit := Z.exit
  anchor_mem := Z.anchor_mem
  entry_mem := Z.entry_mem
  exit_mem := Z.exit_mem
  entry_start := Z.entry_start
  entry_finish := Z.entry_finish
  exit_start := Z.exit_start
  exit_finish := Z.exit_finish
  persistence j := by
    have h := Z.persistence j
    rwa [W.encode_benchmark, W.encode_mixtureValue] at h
  safe_entry := Z.safe_entry.mono (fun q hq => by
    rwa [W.encode_benchmark, W.encode_mixtureValue] at hq)
  safe_exit := Z.safe_exit.mono (fun q hq => by
    rwa [W.encode_benchmark, W.encode_mixtureValue] at hq)
  segments := Z.segments

end Certificate

end WindowInstance

/-- Certificates for all single-arrival windows give certificates for all
windows, with the same level and segment budget. -/
theorem admitsCertificates_of_arrivals {α : ℝ} {L : ℕ → ℕ}
    (h : AdmitsArrivalCertificates α L) : AdmitsCertificates α L :=
  fun _ W => (h _ W.encode W.encode_singleArrivals).map WindowInstance.Certificate.ofEncode

end ConsistentSubmodular
