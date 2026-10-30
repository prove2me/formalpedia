-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:33:46.08903+00:00
-- url     : https://prove2.me/theorems/cb47f0b8-9594-40a2-95d0-a6061f6f00d8
-- title:
--   Relabeling and decomposing decorated finite partitions
-- statement:
--   Decorated partitions can be transported along equivalences of label sets. The finite constructions include partitions on complements, a distinguished root block and its complementary partition, and finite weighted sums of component counts over blocks. A derived class shifts size n to the original size n+1. These are concrete finite objects, maps and counting operations.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledSetOde.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The order isomorphism on finsets induced by an equivalence of labels. -/
noncomputable def finsetOrderIsoOfEquiv {α β : Type*} (e : α ≃ β) :
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

@[simp] lemma finsetOrderIsoOfEquiv_apply {α β : Type*} (e : α ≃ β) (s : Finset α) :
    finsetOrderIsoOfEquiv e s = s.map e.toEmbedding := by
  rfl

@[simp] lemma finsetOrderIsoOfEquiv_symm_apply {α β : Type*} (e : α ≃ β)
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
    ext A
    simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
    constructor
    · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
      subst hBA
      subst hCB
      set_option backward.isDefEq.respectTransparency false in
        simpa [Finset.map_map] using hC
    · intro hA
      refine ⟨(finsetOrderIsoOfEquiv e) A, ?_, ?_⟩
      · exact ⟨A, hA, rfl⟩
      · set_option backward.isDefEq.respectTransparency false in
          simp [Finset.map_map]
  right_inv Q := by
    ext A
    simp only [Finpartition.copy_parts, Finpartition.parts_map, Finset.mem_map]
    constructor
    · rintro ⟨B, ⟨C, hC, hCB⟩, hBA⟩
      subst hBA
      subst hCB
      set_option backward.isDefEq.respectTransparency false in
        simpa [Finset.map_map] using hC
    · intro hA
      refine ⟨(finsetOrderIsoOfEquiv e).symm A, ?_, ?_⟩
      · exact ⟨A, hA, rfl⟩
      · set_option backward.isDefEq.respectTransparency false in
          simp [Finset.map_map]

/-- SET-objects over an arbitrary finite label type. -/
abbrev labelledSetObj (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :=
  Σ P : Finpartition (Finset.univ : Finset α), ∀ B : P.parts, C.Obj B.val.card

/-- The parts of a relabelled full finpartition are equivalent to the original parts. -/
noncomputable def finpartitionUnivCongrParts {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    P.parts ≃ (finpartitionUnivCongr e P).parts where
  toFun B := ⟨(finsetOrderIsoOfEquiv e) B.val, by
    change (finsetOrderIsoOfEquiv e) B.val ∈ (P.map (finsetOrderIsoOfEquiv e)).parts
    rw [Finpartition.parts_map]
    exact Finset.mem_map.mpr ⟨B.val, B.property, rfl⟩⟩
  invFun B := ⟨(finsetOrderIsoOfEquiv e).symm B.val, by
    have hB : B.val ∈ (P.map (finsetOrderIsoOfEquiv e)).parts := by
      simpa [finpartitionUnivCongr] using B.property
    rw [Finpartition.parts_map, Finset.mem_map] at hB
    rcases hB with ⟨A, hA, hAmap⟩
    have hAmap' : (finsetOrderIsoOfEquiv e) A = B.val := by simpa using hAmap
    rw [← hAmap']
    simpa [Finset.map_map] using hA⟩
  left_inv B := by
    ext x
    simp [Finset.map_map]
  right_inv B := by
    ext x
    simp [Finset.map_map]

@[simp] lemma finpartitionUnivCongrParts_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) (B : P.parts) :
    ((finpartitionUnivCongrParts e P B).val.card) = B.val.card := by
  simp [finpartitionUnivCongrParts]

/-- Relabel SET-objects over equivalent finite label types. -/
noncomputable def labelledSetObjCongr (C : CombClass) {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    labelledSetObj C α ≃ labelledSetObj C β :=
  Equiv.sigmaCongr (finpartitionUnivCongr e) fun P =>
    (Equiv.piCongrRight fun B =>
      Equiv.cast (by rw [finpartitionUnivCongrParts_card e P B])).trans
    (Equiv.piCongrLeft (fun B : (finpartitionUnivCongr e P).parts => C.Obj B.val.card)
      (finpartitionUnivCongrParts e P))

@[simp] lemma labelledSetObj_fin_card (C : CombClass) (n : ℕ) :
    Fintype.card (labelledSetObj C (Fin n)) = C.set.counts n := rfl

/-- Weighted SET sum over all partitions of a finite label type. -/
noncomputable def setWeightFull (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] : ℕ :=
  ∑ P : Finpartition (Finset.univ : Finset α), ∏ B : P.parts, C.counts B.val.card

/-- Weighted SET sum over partitions of a finset. -/
noncomputable def setWeightFinset (C : CombClass) {α : Type*} [DecidableEq α]
    (s : Finset α) : ℕ :=
  ∑ P : Finpartition s, ∏ B : P.parts, C.counts B.val.card

@[simp] lemma setWeightFinset_univ (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setWeightFinset C (Finset.univ : Finset α) = setWeightFull C α := rfl

/-- Turn a partition of the complement finset into a partition of the complement subtype. -/
noncomputable def finpartitionSdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
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
        have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
          simpa using hx
        rw [hAempty] at hxsub
        simpa using hxsub))

/-- Turn a partition of the complement subtype back into a partition of the complement finset. -/
noncomputable def finpartitionSubtypeSdiff {α : Type*} [Fintype α] [DecidableEq α]
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
noncomputable def finpartitionSdiffSubtypeCongr {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) :
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

lemma Finpartition.mem_avoid_of_mem_part {α : Type*} [DecidableEq α] {s B A : Finset α}
    {P : Finpartition s} (hB : B ∈ P.parts) :
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
def finEquivNotLast (n : ℕ) : Fin n ≃ {x : Fin (n + 1) // x ≠ Fin.last n} where
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

/-- The labelled derivative class: an object of size `n` is a `C`-object of size `n+1`. -/
def CombClass.deriv (C : CombClass) : CombClass where
  Obj n := C.Obj (n + 1)
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_deriv (C : CombClass) (n : ℕ) :
    C.deriv.counts n = C.counts (n + 1) := rfl

end AnalyticCombinatorics.Ch1


