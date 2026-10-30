-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_SetPartitions_BellMean
-- name    : AnalyticCombinatorics_Ch2_SetPartitions_BellMean
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:12:55.538703+00:00
-- url     : https://prove2.me/theorems/51e4de45-c4a1-4089-9c21-13dfc377820f
-- title:
--   Genuine finite set partitions and adding a distinguished label
-- statement:
--   The Bell number B_n is the cardinality of all Finpartition structures on the full set Fin n. Finite label equivalences induce order isomorphisms on finite subsets and partition correspondences. Root-block and marked-block data describe a partition after adjoining a largest label and the partition on its complementary labels.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/SetPartitions/BellMean.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Bell numbers as finite set partitions

This file uses `Finpartition (Finset.univ : Finset (Fin n))` as the type of genuine
set partitions of `[n]`.
-/

namespace AnalyticCombinatorics.Ch2.SetPartitions

open Finset Function

noncomputable section

-- The equivalences below transport `Finpartition`s through finset/subtype complements;
-- the larger heartbeat budget is for those local `simp`/`grind` calls.
set_option maxHeartbeats 400000

/-- The Bell number as the number of genuine finset partitions of `[n]`. -/
def bellNumber (n : ℕ) : ℕ :=
  Fintype.card (Finpartition (Finset.univ : Finset (Fin n)))

/-- The order isomorphism on finsets induced by an equivalence of labels. -/
private noncomputable def finsetOrderIsoOfEquiv {α β : Type*} (e : α ≃ β) :
    Finset α ≃o Finset β :=
  e.finsetCongr.toOrderIso
    (by
      intro s t h
      rw [Equiv.finsetCongr_apply, Equiv.finsetCongr_apply]
      exact Finset.map_subset_map.mpr h)
    (by
      intro s t h
      rw [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Equiv.finsetCongr_apply]
      exact Finset.map_subset_map.mpr h)

@[simp] private lemma finsetOrderIsoOfEquiv_apply {α β : Type*} (e : α ≃ β)
    (s : Finset α) :
    finsetOrderIsoOfEquiv e s = s.map e.toEmbedding := by
  rfl

@[simp] private lemma finsetOrderIsoOfEquiv_symm_apply {α β : Type*} (e : α ≃ β)
    (s : Finset β) :
    (finsetOrderIsoOfEquiv e).symm s = s.map e.symm.toEmbedding := by
  rfl

/-- Relabel finpartitions of the full label type along an equivalence of labels. -/
noncomputable def finpartitionUnivCongr {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finpartition (Finset.univ : Finset α) ≃ Finpartition (Finset.univ : Finset β) where
  toFun P := (P.map (finsetOrderIsoOfEquiv e)).copy (by
    change (Finset.univ : Finset α).map e.toEmbedding = (Finset.univ : Finset β)
    rw [Finset.map_univ_equiv])
  invFun Q := (Q.map (finsetOrderIsoOfEquiv e).symm).copy (by
    change (Finset.univ : Finset β).map e.symm.toEmbedding = (Finset.univ : Finset α)
    rw [Finset.map_univ_equiv])
  left_inv P := by
    set_option backward.isDefEq.respectTransparency false in
      ext A
      simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
      constructor
      · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
        subst hBA
        subst hCB
        simpa [Finset.map_map] using hC
      · intro hA
        refine ⟨(finsetOrderIsoOfEquiv e) A, ?_, ?_⟩
        · exact ⟨A, hA, rfl⟩
        · simp [Finset.map_map]
  right_inv Q := by
    set_option backward.isDefEq.respectTransparency false in
      ext A
      simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
      constructor
      · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
        subst hBA
        subst hCB
        simpa [Finset.map_map] using hC
      · intro hA
        refine ⟨(finsetOrderIsoOfEquiv e).symm A, ?_, ?_⟩
        · exact ⟨A, hA, rfl⟩
        · simp [Finset.map_map]

/-- Turn a partition of a complement finset into a partition of the complement subtype. -/
private noncomputable def finpartitionSdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    Finpartition (Finset.univ : Finset {x : α // x ∉ B}) :=
  Finpartition.ofExistsUnique
    (Q.parts.image fun A => A.subtype (fun x => x ∉ B))
    (by
      intro p hp x hx
      simp)
    (by
      intro a _ha
      have ha : (a.val : α) ∈ (Finset.univ : Finset α) \ B := by simp [a.property]
      obtain ⟨A, hA, hAuniq⟩ := Q.existsUnique_mem ha
      refine ⟨A.subtype (fun x => x ∉ B), ?_, ?_⟩
      · exact ⟨Finset.mem_image.mpr ⟨A, hA.1, rfl⟩, by simpa using hA.2⟩
      · intro T hT
        rcases Finset.mem_image.mp hT.1 with ⟨A', hA', rfl⟩
        have haA' : (a.val : α) ∈ A' := by simpa using hT.2
        have hAeq : A' = A := hAuniq A' ⟨hA', haA'⟩
        rw [hAeq])
    (by
      intro h
      rcases Finset.mem_image.mp h with ⟨A, hA, hAempty⟩
      exact Q.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        have hxnot : x ∉ B := by
          have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
          simpa using hxcomp
        have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈
            A.subtype (fun x => x ∉ B) := by
          simpa using hx
        rw [hAempty] at hxsub
        simpa using hxsub))

/-- Turn a partition of the complement subtype back into a partition of the complement finset. -/
private noncomputable def finpartitionSubtypeSdiff {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B})) :
    Finpartition ((Finset.univ : Finset α) \ B) :=
  Finpartition.ofExistsUnique
    (Q.parts.image fun A => A.map (Function.Embedding.subtype fun x : α => x ∉ B))
    (by
      intro p hp x hx
      rcases Finset.mem_image.mp hp with ⟨A, _hA, rfl⟩
      rcases Finset.mem_map.mp hx with ⟨a, _ha, rfl⟩
      simp [a.property])
    (by
      intro x hx
      have hxnot : x ∉ B := by simpa using hx
      let a : {x : α // x ∉ B} := ⟨x, hxnot⟩
      obtain ⟨A, hA, hAuniq⟩ := Q.existsUnique_mem (by simp [a])
      refine ⟨A.map (Function.Embedding.subtype fun x : α => x ∉ B), ?_, ?_⟩
      · exact ⟨Finset.mem_image.mpr ⟨A, hA.1, rfl⟩,
          Finset.mem_map.mpr ⟨a, hA.2, rfl⟩⟩
      · intro T hT
        rcases Finset.mem_image.mp hT.1 with ⟨A', hA', rfl⟩
        rcases Finset.mem_map.mp hT.2 with ⟨a', ha', ha'val⟩
        have haeq : a' = a := Subtype.ext (by simpa [a] using ha'val)
        subst haeq
        have hAeq : A' = A := hAuniq A' ⟨hA', ha'⟩
        rw [hAeq])
    (by
      intro h
      rcases Finset.mem_image.mp h with ⟨A, hA, hAempty⟩
      obtain ⟨a, ha⟩ := Q.nonempty_of_mem_parts hA
      have hamap : (a.val : α) ∈ A.map (Function.Embedding.subtype fun x : α => x ∉ B) :=
        Finset.mem_map.mpr ⟨a, ha, rfl⟩
      rw [hAempty] at hamap
      simpa using hamap)

/-- Partitions of a complement finset are the same as partitions of the complement subtype. -/
noncomputable def finpartitionSdiffSubtypeCongr {α : Type*} [Fintype α]
    [DecidableEq α] (B : Finset α) :
    Finpartition ((Finset.univ : Finset α) \ B) ≃
      Finpartition (Finset.univ : Finset {x : α // x ∉ B}) where
  toFun := finpartitionSdiffSubtype B
  invFun := finpartitionSubtypeSdiff B
  left_inv Q := by
    ext A
    simp [finpartitionSdiffSubtype, finpartitionSubtypeSdiff, Finset.mem_subtype,
      Finset.mem_map, Finset.mem_image, Finset.map_map]
    constructor
    · rintro ⟨A', hA'mem, hAeq⟩
      have hfilter : {x ∈ A' | x ∉ B} = A' := by
        ext x
        constructor
        · intro hx
          exact (Finset.mem_filter.mp hx).1
        · intro hx
          exact Finset.mem_filter.mpr
            ⟨hx, by
              have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA'mem hx
              simpa using hxcomp⟩
      rw [← hAeq, hfilter]
      exact hA'mem
    · intro hA
      refine ⟨A, hA, ?_⟩
      ext x
      constructor
      · intro hx
        exact (Finset.mem_filter.mp hx).1
      · intro hx
        exact Finset.mem_filter.mpr
          ⟨hx, by
            have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
            simpa using hxcomp⟩
  right_inv Q := by
    ext A
    simp [finpartitionSdiffSubtype, finpartitionSubtypeSdiff, Finset.mem_subtype,
      Finset.mem_map, Finset.mem_image, Finset.map_map]
    constructor
    · rintro ⟨A', hA'mem, hAeq⟩
      have hsubtype : Finset.subtype (fun x => x ∉ B)
          (A'.map (Function.Embedding.subtype fun x : α => x ∉ B)) = A' := by
        ext x
        simp [x.property]
      rw [← hAeq, hsubtype]
      exact hA'mem
    · intro hA
      refine ⟨A, hA, ?_⟩
      ext x
      simp [x.property]

private lemma Finpartition.mem_avoid_of_mem_part {α : Type*} [DecidableEq α]
    {s B A : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    A ∈ (P.avoid B).parts ↔ A ∈ P.parts ∧ A ≠ B := by
  constructor
  · intro hA
    rcases (Finpartition.mem_avoid P).mp hA with ⟨D, hD, hnle, hDA⟩
    have hDB : D ≠ B := by
      intro h
      exact hnle (by rw [h])
    have hdisj : Disjoint D B := P.disjoint hD hB hDB
    have hsdiff : D \ B = D := Finset.sdiff_eq_self_of_disjoint hdisj
    rw [hsdiff] at hDA
    subst hDA
    exact ⟨hD, hDB⟩
  · rintro ⟨hA, hAB⟩
    have hdisj : Disjoint A B := P.disjoint hA hB hAB
    refine (Finpartition.mem_avoid P).mpr ⟨A, hA, ?_, ?_⟩
    · intro hle
      exact P.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        exact (Finset.disjoint_left.mp hdisj) hx (hle hx))
    · exact Finset.sdiff_eq_self_of_disjoint hdisj

/-- Fixing the root block leaves an arbitrary partition of the complement. -/
noncomputable def finpartitionRootFiberEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) {B : Finset α} (hr : r ∈ B) :
    {P : Finpartition (Finset.univ : Finset α) // P.part r = B} ≃
      Finpartition ((Finset.univ : Finset α) \ B) where
  toFun P := P.val.avoid B
  invFun Q :=
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    let P : Finpartition (Finset.univ : Finset α) :=
      Q.extend hBne disjoint_sdiff_self_left hc
    ⟨P, by
      have hBmem : B ∈ P.parts := by
        simp [P, Finpartition.extend]
      exact P.part_eq_of_mem hBmem hr⟩
  left_inv P := by
    apply Subtype.ext
    ext A
    have hruniv : r ∈ (Finset.univ : Finset α) := by simp
    have hBmem : B ∈ P.val.parts := by
      simpa [P.property] using P.val.part_mem.2 hruniv
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    simp [Finpartition.mem_avoid_of_mem_part hBmem, Finpartition.extend]
    constructor
    · rintro (rfl | hA)
      · exact hBmem
      · exact hA.1
    · intro hA
      by_cases h : A = B
      · exact Or.inl h
      · exact Or.inr ⟨hA, h⟩
  right_inv Q := by
    ext A
    let hBne : B ≠ ∅ := by
      intro h
      simpa [h] using hr
    let hc : (Finset.univ : Finset α) \ B ∪ B = Finset.univ := by
      rw [Finset.sdiff_union_self_eq_union]
      simp
    let P : Finpartition (Finset.univ : Finset α) :=
      Q.extend hBne disjoint_sdiff_self_left hc
    have hBmem : B ∈ P.parts := by
      simp [P, Finpartition.extend]
    have hBnot : B ∉ Q.parts := by
      intro h
      have hrcomp : r ∈ (Finset.univ : Finset α) \ B := Q.subset h hr
      simpa [hr] using hrcomp
    simp [P, Finpartition.extend, hBnot]
    constructor
    · rintro ⟨D, hD, _hnle, hDA⟩
      have hdisj : Disjoint D B := by
        rw [Finset.disjoint_left]
        intro x hxD hxB
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hxD
        exact (by simpa [hxB] using hxcomp)
      have hsdiff : D \ B = D := Finset.sdiff_eq_self_of_disjoint hdisj
      rw [hsdiff] at hDA
      subst hDA
      exact hD
    · intro hA
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hxA
        exact (by simpa [hxB] using hxcomp)
      refine ⟨A, hA, ?_, Finset.sdiff_eq_self_of_disjoint hdisj⟩
      intro hle
      exact Q.ne_empty hA (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro x hx
        exact (Finset.disjoint_left.mp hdisj) hx (hle hx))

/-- `Fin n` is the subtype of `Fin (n+1)` away from the last element. -/
private def finEquivNotLast (n : ℕ) : Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} where
  toFun i := ⟨i.castSucc, Fin.castSucc_ne_last i⟩
  invFun x := Fin.castPred x.val x.property
  left_inv i := by
    exact Fin.castPred_castSucc
  right_inv x := by
    apply Subtype.ext
    exact (Fin.castSucc_castPred x.val x.property).symm

/-- Subsets of `Fin n` correspond to subsets of `Fin (n+1)` containing `Fin.last n`. -/
noncomputable def rootBlockEquiv (n : ℕ) :
    Finset (Fin n) ≃ {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} where
  toFun S := ⟨insert (Fin.last n) (S.map Fin.castSuccEmb), by simp⟩
  invFun B := (B.val.subtype fun x => x ≠ Fin.last n).map (finEquivNotLast n).symm.toEmbedding
  left_inv S := by
    ext i
    simp [finEquivNotLast]
  right_inv B := by
    apply Subtype.ext
    ext x
    by_cases hx : x = Fin.last n
    · subst hx
      simpa using B.property
    · have hx' :
        (⟨x, hx⟩ : {x : Fin (n + 1) // x ≠ Fin.last n}) ∈
            B.val.subtype (fun x => x ≠ Fin.last n) ↔ x ∈ B.val := by
        constructor
        · intro h
          simpa using h
        · intro h
          exact Finset.mem_subtype.mpr h
      simp [finEquivNotLast, hx]
      constructor
      · rintro ⟨a, ha, hax⟩
        rw [← hax]
        exact ha
      · intro hxB
        refine ⟨Fin.castPred x hx, ?_, ?_⟩
        · rwa [Fin.castSucc_castPred]
        · exact Fin.castSucc_castPred x hx

abbrev MarkedBlock (n : ℕ) :=
  Σ P : Finpartition (Finset.univ : Finset (Fin n)), P.parts

noncomputable def markedBlockMap (n : ℕ) :
    MarkedBlock n → {A : Finset (Fin n) // A.Nonempty} :=
  fun x => ⟨x.2.val, Finpartition.nonempty_of_mem_parts x.1 x.2.property⟩

noncomputable def markedBlockFiberEquiv (n : ℕ)
    (A : {A : Finset (Fin n) // A.Nonempty}) :
    {x : MarkedBlock n // markedBlockMap n x = A} ≃
      {P : Finpartition (Finset.univ : Finset (Fin n)) // P.part A.property.choose = A.val} :=
  let a : Fin n := A.property.choose
  let ha : a ∈ A.val := A.property.choose_spec
  { toFun := fun x => ⟨x.val.1, by
      have hval : x.val.2.val = A.val := congrArg Subtype.val x.property
      have haBlock : a ∈ x.val.2.val := by simpa [hval] using ha
      calc
        x.val.1.part a = x.val.2.val := x.val.1.part_eq_of_mem x.val.2.property haBlock
        _ = A.val := hval⟩
    invFun := fun P =>
      ⟨⟨P.val, ⟨A.val, by
        have hmem : P.val.part A.property.choose ∈ P.val.parts := P.val.part_mem.2 (by simp)
        convert hmem using 1
        exact P.property.symm⟩⟩, by
        apply Subtype.ext
        rfl⟩
    left_inv := by
      rintro ⟨⟨P, B⟩, hx⟩
      apply Subtype.ext
      cases B with
      | mk B hB =>
        dsimp at hx ⊢
        have hval : B = A.val := congrArg Subtype.val hx
        subst hval
        simp
    right_inv := by
      intro P
      apply Subtype.ext
      rfl }

end

end AnalyticCombinatorics.Ch2.SetPartitions


