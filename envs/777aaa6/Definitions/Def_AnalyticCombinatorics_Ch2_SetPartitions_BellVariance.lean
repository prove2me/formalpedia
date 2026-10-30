-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_SetPartitions_BellVariance
-- name    : AnalyticCombinatorics_Ch2_SetPartitions_BellVariance
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:13:57.367183+00:00
-- url     : https://prove2.me/theorems/dde45036-94eb-41ea-8f49-04151e85cc25
-- title:
--   Adding and deleting the largest label in a finite set partition
-- statement:
--   Partitions are Finpartition structures on Fin n. Finite subset maps lift old labels and delete the last label. A new partition is obtained either by adding a singleton block or by joining the new label to a chosen old block. The inverse deletes the last label and records that choice; these operations form a finite correspondence for weighted block counts.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/SetPartitions/BellVariance.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Second moment and variance for Bell set partitions

This file refines the add-one-element fiber count from the first-moment Bell
identity to a weighted identity, then derives the second moment and variance.
-/

namespace AnalyticCombinatorics.Ch2.SetPartitions.BellVariance

open Finset Function

noncomputable section

-- The local `Finpartition.ofExistsUnique` fiber constructors create large goals.
set_option maxHeartbeats 400000

abbrev Partition (n : ℕ) :=
  Finpartition (Finset.univ : Finset (Fin n))

def liftBlock (n : ℕ) (A : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  A.map Fin.castSuccEmb

private lemma liftBlock_injective (n : ℕ) :
    Function.Injective (liftBlock n) := by
  intro A B h
  simpa [liftBlock] using h

def liftBlockEmb (n : ℕ) : Finset (Fin n) ↪ Finset (Fin (n + 1)) where
  toFun := liftBlock n
  inj' := liftBlock_injective n

private noncomputable def dropBlock (n : ℕ) (A : Finset (Fin (n + 1))) :
    Finset (Fin n) :=
  A.preimage Fin.castSucc (Fin.castSucc_injective n).injOn

@[simp] lemma liftBlockEmb_apply (n : ℕ) (A : Finset (Fin n)) :
    liftBlockEmb n A = liftBlock n A := by
  rfl

@[simp] private lemma mem_liftBlock (n : ℕ) (A : Finset (Fin n)) (i : Fin n) :
    i.castSucc ∈ liftBlock n A ↔ i ∈ A := by
  simp [liftBlock]

@[simp] lemma last_notMem_liftBlock (n : ℕ) (A : Finset (Fin n)) :
    Fin.last n ∉ liftBlock n A := by
  simp [liftBlock]

@[simp] private lemma mem_dropBlock (n : ℕ) (A : Finset (Fin (n + 1))) (i : Fin n) :
    i ∈ dropBlock n A ↔ i.castSucc ∈ A := by
  simp [dropBlock]

@[simp] private lemma dropBlock_liftBlock (n : ℕ) (A : Finset (Fin n)) :
    dropBlock n (liftBlock n A) = A := by
  ext i
  simp

@[simp] private lemma dropBlock_singleton_last (n : ℕ) :
    dropBlock n ({Fin.last n} : Finset (Fin (n + 1))) = ∅ := by
  ext i
  simp

@[simp] private lemma dropBlock_insert_last_liftBlock (n : ℕ) (A : Finset (Fin n)) :
    dropBlock n (insert (Fin.last n) (liftBlock n A)) = A := by
  ext i
  simp

private lemma liftBlock_eq_empty_iff (n : ℕ) (A : Finset (Fin n)) :
    liftBlock n A = ∅ ↔ A = ∅ := by
  simp [liftBlock]

noncomputable def singletonChild (n : ℕ) (P : Partition n) : Partition (n + 1) :=
  Finpartition.ofExistsUnique
    (insert ({Fin.last n} : Finset (Fin (n + 1))) (P.parts.map (liftBlockEmb n)))
    (by
      intro B hB x hx
      simp)
    (by
      intro x _hx
      rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
      · obtain ⟨A, hA, hAuniq⟩ := P.existsUnique_mem (by simp : i ∈ (Finset.univ : Finset (Fin n)))
        refine ⟨liftBlock n A, ?_, ?_⟩
        · refine ⟨?_, by simpa using hA.2⟩
          exact Finset.mem_insert.mpr
            (Or.inr (Finset.mem_map.mpr ⟨A, hA.1, rfl⟩))
        · intro T hT
          rcases Finset.mem_insert.mp hT.1 with (hTlast | hTlift)
          · have hnot : (i.castSucc : Fin (n + 1)) ∉ ({Fin.last n} : Finset (Fin (n + 1))) := by
              simp
            exact False.elim (hnot (by simpa [hTlast] using hT.2))
          · rcases Finset.mem_map.mp hTlift with ⟨B, hB, hBT⟩
            have hiB : i ∈ B := by
              have hiBT : i.castSucc ∈ (liftBlockEmb n) B := by
                rw [hBT]
                exact hT.2
              simpa [liftBlockEmb_apply] using hiBT
            have hBA : B = A := hAuniq B ⟨hB, hiB⟩
            rw [← hBT, hBA]
            simp
      · refine ⟨({Fin.last n} : Finset (Fin (n + 1))), ?_, ?_⟩
        · simp
        · intro T hT
          rcases Finset.mem_insert.mp hT.1 with (hTlast | hTlift)
          · exact hTlast
          · rcases Finset.mem_map.mp hTlift with ⟨B, _hB, hBT⟩
            have hlast : Fin.last n ∈ liftBlock n B := by
              have hlastB : Fin.last n ∈ (liftBlockEmb n) B := by
                rw [hBT]
                exact hT.2
              rw [liftBlockEmb_apply] at hlastB
              exact hlastB
            exact False.elim (last_notMem_liftBlock n B hlast))
    (by
      intro h
      rcases Finset.mem_insert.mp h with (hsing | hlift)
      · simp at hsing
      · rcases Finset.mem_map.mp hlift with ⟨A, hA, hAempty⟩
        exact P.empty_notMem_parts (by
          have : A = ∅ := (liftBlock_eq_empty_iff n A).mp (by simpa [liftBlockEmb_apply] using hAempty)
          rw [this] at hA
          exact hA))

@[simp] lemma singletonChild_parts (n : ℕ) (P : Partition n) :
    (singletonChild n P).parts =
      insert ({Fin.last n} : Finset (Fin (n + 1))) (P.parts.map (liftBlockEmb n)) := by
  rfl

noncomputable def joinChild (n : ℕ) (P : Partition n) (A : P.parts) :
    Partition (n + 1) :=
  Finpartition.ofExistsUnique
    (insert (insert (Fin.last n) (liftBlock n A.val))
      ((P.parts.erase A.val).map (liftBlockEmb n)))
    (by
      intro B hB x hx
      simp)
    (by
      intro x _hx
      rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
      · obtain ⟨C, hC, hCuniq⟩ := P.existsUnique_mem (by simp : i ∈ (Finset.univ : Finset (Fin n)))
        by_cases hCA : C = A.val
        · refine ⟨insert (Fin.last n) (liftBlock n A.val), ?_, ?_⟩
          · refine ⟨by simp, ?_⟩
            simp [hCA.symm, hC.2]
          · intro T hT
            rcases Finset.mem_insert.mp hT.1 with (hTjoin | hTlift)
            · exact hTjoin
            · rcases Finset.mem_map.mp hTlift with ⟨D, hD, hDT⟩
              have hiD : i ∈ D := by
                have hiDT : i.castSucc ∈ (liftBlockEmb n) D := by
                  rw [hDT]
                  exact hT.2
                simpa [liftBlockEmb_apply] using hiDT
              have hDC : D = C := hCuniq D ⟨(Finset.mem_erase.mp hD).2, hiD⟩
              exact False.elim ((Finset.mem_erase.mp hD).1 (by rw [hDC, hCA]))
        · refine ⟨liftBlock n C, ?_, ?_⟩
          · refine ⟨?_, by simpa using hC.2⟩
            exact Finset.mem_insert.mpr
              (Or.inr (Finset.mem_map.mpr ⟨C, Finset.mem_erase.mpr ⟨hCA, hC.1⟩, rfl⟩))
          · intro T hT
            rcases Finset.mem_insert.mp hT.1 with (hTjoin | hTlift)
            · have hiA : i ∈ A.val := by
                simpa [hTjoin] using hT.2
              exact False.elim (hCA (hCuniq A.val ⟨A.property, hiA⟩).symm)
            · rcases Finset.mem_map.mp hTlift with ⟨D, hD, hDT⟩
              have hiD : i ∈ D := by
                have hiDT : i.castSucc ∈ (liftBlockEmb n) D := by
                  rw [hDT]
                  exact hT.2
                simpa [liftBlockEmb_apply] using hiDT
              have hDC : D = C := hCuniq D ⟨(Finset.mem_erase.mp hD).2, hiD⟩
              rw [← hDT, hDC]
              simp
      · refine ⟨insert (Fin.last n) (liftBlock n A.val), ?_, ?_⟩
        · simp
        · intro T hT
          rcases Finset.mem_insert.mp hT.1 with (hTjoin | hTlift)
          · exact hTjoin
          · rcases Finset.mem_map.mp hTlift with ⟨D, _hD, hDT⟩
            have hlast : Fin.last n ∈ liftBlock n D := by
              have hlastD : Fin.last n ∈ (liftBlockEmb n) D := by
                rw [hDT]
                exact hT.2
              rw [liftBlockEmb_apply] at hlastD
              exact hlastD
            exact False.elim (last_notMem_liftBlock n D hlast))
    (by
      intro h
      rcases Finset.mem_insert.mp h with (hjoin | hlift)
      · have hlast : Fin.last n ∈ (∅ : Finset (Fin (n + 1))) := by
          rw [hjoin]
          simp
        exact Finset.notMem_empty (Fin.last n) hlast
      · rcases Finset.mem_map.mp hlift with ⟨B, hB, hBempty⟩
        have hBval : B = ∅ := (liftBlock_eq_empty_iff n B).mp (by
          simpa [liftBlockEmb_apply] using hBempty)
        exact P.empty_notMem_parts (by
          have hBmem : B ∈ P.parts := (Finset.mem_erase.mp hB).2
          rw [hBval] at hBmem
          exact hBmem))

@[simp] lemma joinChild_parts (n : ℕ) (P : Partition n) (A : P.parts) :
    (joinChild n P A).parts =
      insert (insert (Fin.last n) (liftBlock n A.val))
        ((P.parts.erase A.val).map (liftBlockEmb n)) := by
  rfl

private noncomputable def deleteLastPartition (n : ℕ) (Q : Partition (n + 1)) : Partition n :=
  Finpartition.ofExistsUnique
    ((Q.parts.image (dropBlock n)).erase ∅)
    (by
      intro B hB x hx
      simp)
    (by
      intro i _hi
      obtain ⟨B, hB, hBuniq⟩ :=
        Q.existsUnique_mem (by simp : i.castSucc ∈ (Finset.univ : Finset (Fin (n + 1))))
      refine ⟨dropBlock n B, ?_, ?_⟩
      · refine ⟨?_, by simpa using hB.2⟩
        exact Finset.mem_erase.mpr
          ⟨by
            intro hempty
            have hiDrop : i ∈ dropBlock n B := by simpa using hB.2
            rw [hempty] at hiDrop
            exact Finset.notMem_empty i hiDrop,
            Finset.mem_image.mpr ⟨B, hB.1, rfl⟩⟩
      · intro T hT
        have hTmem : T ∈ Q.parts.image (dropBlock n) := (Finset.mem_erase.mp hT.1).2
        rcases Finset.mem_image.mp hTmem with ⟨C, hC, hCT⟩
        have hiC : i.castSucc ∈ C := by
          have hiDrop : i ∈ dropBlock n C := by
            rw [hCT]
            exact hT.2
          simpa using hiDrop
        have hCB : C = B := hBuniq C ⟨hC, hiC⟩
        rw [← hCT, hCB])
    (by simp)

@[simp] private lemma deleteLastPartition_parts (n : ℕ) (Q : Partition (n + 1)) :
    (deleteLastPartition n Q).parts = (Q.parts.image (dropBlock n)).erase ∅ := by
  rfl

@[simp] private lemma deleteLastPartition_singletonChild (n : ℕ) (P : Partition n) :
    deleteLastPartition n (singletonChild n P) = P := by
  ext A
  constructor
  · intro hA
    rw [deleteLastPartition_parts, singletonChild_parts] at hA
    rcases Finset.mem_erase.mp hA with ⟨hAne, hAimg⟩
    rcases Finset.mem_image.mp hAimg with ⟨B, hB, hBA⟩
    rcases Finset.mem_insert.mp hB with (hBsing | hBlift)
    · rw [hBsing] at hBA
      simp at hBA
      exact False.elim (hAne hBA.symm)
    · rcases Finset.mem_map.mp hBlift with ⟨C, hC, hCB⟩
      have hdrop : dropBlock n B = C := by
        rw [← hCB]
        simp
      rw [← hBA, hdrop]
      exact hC
  · intro hA
    rw [deleteLastPartition_parts, singletonChild_parts]
    refine Finset.mem_erase.mpr ⟨P.ne_empty hA, ?_⟩
    exact Finset.mem_image.mpr
      ⟨liftBlock n A,
        Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨A, hA, rfl⟩)),
        by simp⟩

@[simp] private lemma deleteLastPartition_joinChild (n : ℕ) (P : Partition n) (A : P.parts) :
    deleteLastPartition n (joinChild n P A) = P := by
  ext B
  constructor
  · intro hB
    rw [deleteLastPartition_parts, joinChild_parts] at hB
    rcases Finset.mem_erase.mp hB with ⟨hBne, hBimg⟩
    rcases Finset.mem_image.mp hBimg with ⟨C, hC, hCB⟩
    rcases Finset.mem_insert.mp hC with (hCjoin | hClift)
    · rw [hCjoin] at hCB
      simp at hCB
      rw [← hCB]
      exact A.property
    · rcases Finset.mem_map.mp hClift with ⟨D, hD, hDC⟩
      have hdrop : dropBlock n C = D := by
        rw [← hDC]
        simp
      rw [← hCB, hdrop]
      exact (Finset.mem_erase.mp hD).2
  · intro hB
    rw [deleteLastPartition_parts, joinChild_parts]
    by_cases hBA : B = A.val
    · refine Finset.mem_erase.mpr ⟨P.ne_empty hB, ?_⟩
      exact Finset.mem_image.mpr
        ⟨insert (Fin.last n) (liftBlock n A.val), by simp, by simp [hBA]⟩
    · refine Finset.mem_erase.mpr ⟨P.ne_empty hB, ?_⟩
      exact Finset.mem_image.mpr
        ⟨liftBlock n B,
          Finset.mem_insert.mpr
            (Or.inr (Finset.mem_map.mpr ⟨B, Finset.mem_erase.mpr ⟨hBA, hB⟩, rfl⟩)),
          by simp⟩

private lemma liftBlock_dropBlock_eq_of_last_notMem (n : ℕ) {B : Finset (Fin (n + 1))}
    (hlast : Fin.last n ∉ B) :
    liftBlock n (dropBlock n B) = B := by
  ext x
  rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
  · simp
  · simp [hlast]

private lemma part_last_eq_singleton_of_dropBlock_eq_empty (n : ℕ) (Q : Partition (n + 1))
    (hroot : dropBlock n (Q.part (Fin.last n)) = ∅) :
    Q.part (Fin.last n) = ({Fin.last n} : Finset (Fin (n + 1))) := by
  ext x
  rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
  · have : i ∉ dropBlock n (Q.part (Fin.last n)) := by
      rw [hroot]
      simp
    constructor
    · intro hi
      exact False.elim (this (by simpa using hi))
    · intro hi
      simp at hi
  · simp

private lemma part_last_eq_insert_lift_dropBlock (n : ℕ) (Q : Partition (n + 1)) :
    Q.part (Fin.last n) =
      insert (Fin.last n) (liftBlock n (dropBlock n (Q.part (Fin.last n)))) := by
  ext x
  rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
  · simp
  · simp

private lemma last_notMem_of_ne_part_last (n : ℕ) (Q : Partition (n + 1))
    {B : Finset (Fin (n + 1))} (hB : B ∈ Q.parts) (hne : B ≠ Q.part (Fin.last n)) :
    Fin.last n ∉ B := by
  intro hlast
  exact hne (Q.part_eq_of_mem hB hlast).symm

private lemma dropBlock_ne_empty_of_last_notMem (n : ℕ) (Q : Partition (n + 1))
    {B : Finset (Fin (n + 1))} (hB : B ∈ Q.parts) (hlast : Fin.last n ∉ B) :
    dropBlock n B ≠ ∅ := by
  obtain ⟨x, hx⟩ := Q.nonempty_of_mem_parts hB
  rcases Fin.eq_castSucc_or_eq_last x with (⟨i, rfl⟩ | rfl)
  · exact Finset.ne_empty_of_mem (by simpa using hx)
  · exact False.elim (hlast hx)

private lemma rootDrop_mem_deleteLastPartition (n : ℕ) (Q : Partition (n + 1))
    (hroot : dropBlock n (Q.part (Fin.last n)) ≠ ∅) :
    dropBlock n (Q.part (Fin.last n)) ∈ (deleteLastPartition n Q).parts := by
  rw [deleteLastPartition_parts]
  exact Finset.mem_erase.mpr
    ⟨hroot, Finset.mem_image.mpr
      ⟨Q.part (Fin.last n), Q.part_mem.2 (by simp), rfl⟩⟩

private lemma singletonChild_deleteLastPartition_of_rootDrop_empty (n : ℕ)
    (Q : Partition (n + 1)) (hroot : dropBlock n (Q.part (Fin.last n)) = ∅) :
    singletonChild n (deleteLastPartition n Q) = Q := by
  ext B
  constructor
  · intro hB
    rw [singletonChild_parts] at hB
    rcases Finset.mem_insert.mp hB with (hBsing | hBlift)
    · rw [hBsing]
      rw [← part_last_eq_singleton_of_dropBlock_eq_empty n Q hroot]
      exact Q.part_mem.2 (by simp)
    · rcases Finset.mem_map.mp hBlift with ⟨D, hD, hDB⟩
      rw [deleteLastPartition_parts] at hD
      rcases Finset.mem_erase.mp hD with ⟨hDne, hDimg⟩
      rcases Finset.mem_image.mp hDimg with ⟨C, hC, hCD⟩
      have hCne : C ≠ Q.part (Fin.last n) := by
        intro hCroot
        exact hDne (by rw [← hCD, hCroot, hroot])
      have hlastC : Fin.last n ∉ C := last_notMem_of_ne_part_last n Q hC hCne
      rw [← hDB, ← hCD, liftBlockEmb_apply,
        liftBlock_dropBlock_eq_of_last_notMem n hlastC]
      exact hC
  · intro hB
    rw [singletonChild_parts]
    by_cases hBroot : B = Q.part (Fin.last n)
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      rw [hBroot, part_last_eq_singleton_of_dropBlock_eq_empty n Q hroot]
    · have hlastB : Fin.last n ∉ B := last_notMem_of_ne_part_last n Q hB hBroot
      refine Finset.mem_insert.mpr (Or.inr ?_)
      refine Finset.mem_map.mpr ⟨dropBlock n B, ?_, ?_⟩
      · rw [deleteLastPartition_parts]
        exact Finset.mem_erase.mpr
          ⟨dropBlock_ne_empty_of_last_notMem n Q hB hlastB,
            Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩
      · rw [liftBlockEmb_apply]
        exact liftBlock_dropBlock_eq_of_last_notMem n hlastB

private lemma dropBlock_ne_rootDrop_of_ne_part_last (n : ℕ) (Q : Partition (n + 1))
    {B : Finset (Fin (n + 1))} (hB : B ∈ Q.parts) (hBroot : B ≠ Q.part (Fin.last n)) :
    dropBlock n B ≠ dropBlock n (Q.part (Fin.last n)) := by
  intro hdrop
  have hlastB : Fin.last n ∉ B := last_notMem_of_ne_part_last n Q hB hBroot
  have hrootNonempty : (dropBlock n (Q.part (Fin.last n))).Nonempty := by
    have hlast : Fin.last n ∈ Q.part (Fin.last n) := Q.mem_part (by simp)
    have hrootPart : Q.part (Fin.last n) ≠ ∅ := by
      exact Finset.ne_empty_of_mem hlast
    by_contra hempty
    have hrootSingleton :
        Q.part (Fin.last n) = ({Fin.last n} : Finset (Fin (n + 1))) :=
      part_last_eq_singleton_of_dropBlock_eq_empty n Q (Finset.not_nonempty_iff_eq_empty.mp hempty)
    have hrootOnly : Q.part (Fin.last n) = {Fin.last n} := hrootSingleton
    have hdropBempty : dropBlock n B = ∅ := by
      rw [hdrop, Finset.not_nonempty_iff_eq_empty.mp hempty]
    have hBempty : B = ∅ := by
      rw [← liftBlock_dropBlock_eq_of_last_notMem n hlastB, hdropBempty]
      simp [liftBlock]
    exact Q.ne_empty hB hBempty
  obtain ⟨i, hiRoot⟩ := hrootNonempty
  have hiB : i.castSucc ∈ B := by
    have : i ∈ dropBlock n B := by rwa [hdrop]
    simpa using this
  have hiRootPart : i.castSucc ∈ Q.part (Fin.last n) := by simpa using hiRoot
  have hEq : B = Q.part (Fin.last n) :=
    Q.eq_of_mem_parts hB (Q.part_mem.2 (by simp)) hiB hiRootPart
  exact hBroot hEq

private lemma joinChild_deleteLastPartition_of_rootDrop_nonempty (n : ℕ)
    (Q : Partition (n + 1)) (hroot : dropBlock n (Q.part (Fin.last n)) ≠ ∅) :
    joinChild n (deleteLastPartition n Q)
      ⟨dropBlock n (Q.part (Fin.last n)), rootDrop_mem_deleteLastPartition n Q hroot⟩ = Q := by
  ext B
  constructor
  · intro hB
    rw [joinChild_parts] at hB
    rcases Finset.mem_insert.mp hB with (hBjoin | hBlift)
    · rw [hBjoin]
      rw [← part_last_eq_insert_lift_dropBlock n Q]
      exact Q.part_mem.2 (by simp)
    · rcases Finset.mem_map.mp hBlift with ⟨D, hD, hDB⟩
      rcases Finset.mem_erase.mp hD with ⟨hDneRoot, hDmem⟩
      rw [deleteLastPartition_parts] at hDmem
      rcases Finset.mem_erase.mp hDmem with ⟨_hDne, hDimg⟩
      rcases Finset.mem_image.mp hDimg with ⟨C, hC, hCD⟩
      have hCne : C ≠ Q.part (Fin.last n) := by
        intro hCroot
        exact hDneRoot (by rw [← hCD, hCroot])
      have hlastC : Fin.last n ∉ C := last_notMem_of_ne_part_last n Q hC hCne
      rw [← hDB, ← hCD, liftBlockEmb_apply,
        liftBlock_dropBlock_eq_of_last_notMem n hlastC]
      exact hC
  · intro hB
    rw [joinChild_parts]
    by_cases hBroot : B = Q.part (Fin.last n)
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      subst B
      exact part_last_eq_insert_lift_dropBlock n Q
    · have hlastB : Fin.last n ∉ B := last_notMem_of_ne_part_last n Q hB hBroot
      refine Finset.mem_insert.mpr (Or.inr ?_)
      refine Finset.mem_map.mpr ⟨dropBlock n B, ?_, ?_⟩
      · refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · exact dropBlock_ne_rootDrop_of_ne_part_last n Q hB hBroot
        · rw [deleteLastPartition_parts]
          exact Finset.mem_erase.mpr
            ⟨dropBlock_ne_empty_of_last_notMem n Q hB hlastB,
              Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩
      · rw [liftBlockEmb_apply]
        exact liftBlock_dropBlock_eq_of_last_notMem n hlastB

abbrev AddFiber (n : ℕ) :=
  Σ P : Partition n, Option P.parts

private noncomputable def rootChoice (n : ℕ) (Q : Partition (n + 1)) :
    Option (deleteLastPartition n Q).parts :=
  if h : dropBlock n (Q.part (Fin.last n)) = ∅ then
    none
  else
    some ⟨dropBlock n (Q.part (Fin.last n)), rootDrop_mem_deleteLastPartition n Q h⟩

noncomputable def addLastChoice (n : ℕ) : AddFiber n → Partition (n + 1)
  | ⟨P, none⟩ => singletonChild n P
  | ⟨P, some A⟩ => joinChild n P A

private noncomputable def deleteLastChoice (n : ℕ) (Q : Partition (n + 1)) : AddFiber n :=
  ⟨deleteLastPartition n Q, rootChoice n Q⟩

private lemma sigmaOptionNone_ext {n : ℕ} {P Q : Partition n} (h : P = Q) :
    (⟨P, (none : Option P.parts)⟩ : AddFiber n) = ⟨Q, none⟩ := by
  cases h
  rfl

private lemma sigmaOptionSome_ext {n : ℕ} {P Q : Partition n} (h : P = Q)
    (A' : P.parts) (A : Q.parts) (hval : A'.val = A.val) :
    (⟨P, some A'⟩ : AddFiber n) = ⟨Q, some A⟩ := by
  cases h
  exact congrArg (fun B : P.parts => (⟨P, some B⟩ : AddFiber n)) (Subtype.ext hval)

@[simp] private lemma addLastChoice_none (n : ℕ) (P : Partition n) :
    addLastChoice n ⟨P, none⟩ = singletonChild n P := by
  rfl

@[simp] private lemma addLastChoice_some (n : ℕ) (P : Partition n) (A : P.parts) :
    addLastChoice n ⟨P, some A⟩ = joinChild n P A := by
  rfl

@[simp] private lemma rootChoice_singletonChild (n : ℕ) (P : Partition n) :
    rootChoice n (singletonChild n P) = none := by
  have hpart :
      (singletonChild n P).part (Fin.last n) =
        ({Fin.last n} : Finset (Fin (n + 1))) := by
    exact (singletonChild n P).part_eq_of_mem (by simp) (by simp)
  simp [rootChoice, hpart]

@[simp] private lemma rootChoice_joinChild (n : ℕ) (P : Partition n) (A : P.parts) :
    rootChoice n (joinChild n P A) =
      some ⟨A.val, by
        rw [deleteLastPartition_joinChild n P A]
        exact A.property⟩ := by
  have hpart :
      (joinChild n P A).part (Fin.last n) =
        insert (Fin.last n) (liftBlock n A.val) := by
    exact (joinChild n P A).part_eq_of_mem (by simp) (by simp)
  have hdrop :
      dropBlock n ((joinChild n P A).part (Fin.last n)) = A.val := by
    rw [hpart]
    simp
  have hAne : A.val ≠ ∅ := P.ne_empty A.property
  unfold rootChoice
  split
  · rename_i h
    exact False.elim (hAne (by rw [← hdrop, h]))
  · apply congrArg some
    apply Subtype.ext
    exact hdrop

private lemma deleteLastChoice_addLastChoice (n : ℕ) (x : AddFiber n) :
    deleteLastChoice n (addLastChoice n x) = x := by
  rcases x with ⟨P, o⟩
  cases o with
  | none =>
      change
        (⟨deleteLastPartition n (singletonChild n P),
            rootChoice n (singletonChild n P)⟩ : AddFiber n) =
          ⟨P, none⟩
      rw [rootChoice_singletonChild]
      exact sigmaOptionNone_ext (deleteLastPartition_singletonChild n P)
  | some A =>
      change
        (⟨deleteLastPartition n (joinChild n P A),
            rootChoice n (joinChild n P A)⟩ : AddFiber n) =
          ⟨P, some A⟩
      rw [rootChoice_joinChild]
      exact sigmaOptionSome_ext (deleteLastPartition_joinChild n P A)
        ⟨A.val, by
          rw [deleteLastPartition_joinChild n P A]
          exact A.property⟩ A rfl

private lemma addLastChoice_deleteLastChoice (n : ℕ) (Q : Partition (n + 1)) :
    addLastChoice n (deleteLastChoice n Q) = Q := by
  by_cases h : dropBlock n (Q.part (Fin.last n)) = ∅
  · change addLastChoice n ⟨deleteLastPartition n Q, rootChoice n Q⟩ = Q
    simp [rootChoice, h, addLastChoice]
    exact singletonChild_deleteLastPartition_of_rootDrop_empty n Q h
  · change addLastChoice n ⟨deleteLastPartition n Q, rootChoice n Q⟩ = Q
    simp [rootChoice, h, addLastChoice]
    exact joinChild_deleteLastPartition_of_rootDrop_nonempty n Q h

noncomputable def addLastEquiv (n : ℕ) : AddFiber n ≃ Partition (n + 1) where
  toFun := addLastChoice n
  invFun := deleteLastChoice n
  left_inv := deleteLastChoice_addLastChoice n
  right_inv := addLastChoice_deleteLastChoice n

end

end AnalyticCombinatorics.Ch2.SetPartitions.BellVariance


