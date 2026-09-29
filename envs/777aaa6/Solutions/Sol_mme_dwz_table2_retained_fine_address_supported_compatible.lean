-- Prove2me | solution 1 for mme_dwz_table2_retained_fine_address_supported_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:31:21.804838+00:00
-- url     : https://prove2.me/submissions/f04179ed-9735-4bfc-89b9-ba9ecc508dc1

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Theorems.Thm_mme_dwz_table2_retained_fine_address_xy_owner
import Theorems.Thm_mme_dwz_table2_step1_fine_support_implies_grouped_compatibility

open MME
open MME.DWZStep1Support
open MME.DWZStep1Histogram
open MME.DWZStep2Source

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (K : Type u) [Field K] (q m : ℕ)
    {Copy Position : Type*} [Fintype Position]
    (outer : Copy → Position → Fin 15)
    (left right : Copy → Fin 3 → Position → Fin 3)
    (hCoarse : ∀ j i r,
      (left j i r).val + (right j i r).val =
        (cwSquareBlockType
          (DWZSquare.shapeX (outer j r))
          (DWZSquare.shapeY (outer j r))
          (DWZSquare.shapeZ (outer j r)) i).val)
    (hCommonZ : ∀ j j' r,
      DWZSquare.shapeZ (outer j r) = DWZSquare.shapeZ (outer j' r))
    (hYIsolated : ∀ j j',
      (fun r ↦ DWZSquare.shapeY (outer j r)) =
        (fun r ↦ DWZSquare.shapeY (outer j' r)) → j = j')
    (hXSurvives : ∀ j (s : Fin 15), DWZSquare.shapeY s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧ (left j 0 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hYSurvives : ∀ j (s : Fin 15), DWZSquare.shapeX s = 0 →
      ∀ a : Fin 3,
        Fintype.card {t : Position //
          outer j t = s ∧ (left j 1 t).val + a.val = 2} =
          MME.DWZTable2Counts.split s a * m)
    (hTotal : ∀ j (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber (outer j) (left j 2) k a) =
        table2TotalZSplit k a * m) :
    ∀ js : Fin 3 → Copy,
      (∀ r : Position,
        (cwSquareFineSplitGrading K q).blockTensor
          (fun i ↦ retainedFineAddress left right (js i) i r) ≠ 0) →
      retainedFineCompatible m outer
        (retainedFineAddress left right (js 2) 2) (js 0) := by
  intro js hSupported
  have hXY : js 0 = js 1 :=
    mme_dwz_table2_retained_fine_address_xy_owner K q outer left right
      hCoarse hCommonZ hYIsolated js hSupported
  have hCoarseMixed : ∀ i t,
      (left (js i) i t).val + (right (js i) i t).val =
        (![DWZSquare.shapeX (outer (js 0) t),
          DWZSquare.shapeY (outer (js 0) t),
          DWZSquare.shapeZ (outer (js 0) t)] i).val := by
    intro i t
    fin_cases i
    · change (left (js 0) 0 t).val + (right (js 0) 0 t).val =
        (DWZSquare.shapeX (outer (js 0) t)).val
      simpa only [cwSquareBlockType] using hCoarse (js 0) 0 t
    · change (left (js 1) 1 t).val + (right (js 1) 1 t).val =
        (DWZSquare.shapeY (outer (js 0) t)).val
      have h := hCoarse (js 1) 1 t
      simp only [cwSquareBlockType] at h
      simpa only [hXY] using h
    · change (left (js 2) 2 t).val + (right (js 2) 2 t).val =
        (DWZSquare.shapeZ (outer (js 0) t)).val
      calc
        _ = (DWZSquare.shapeZ (outer (js 2) t)).val := by
          simpa only [cwSquareBlockType] using hCoarse (js 2) 2 t
        _ = _ := congrArg Fin.val (hCommonZ (js 2) (js 0) t)
  have hTotalMixed : ∀ (k : Fin 5) (a : Fin 3),
      Fintype.card (TotalZFiber (outer (js 0)) (left (js 2) 2) k a) =
        table2TotalZSplit k a * m := by
    intro k a
    let e :
        TotalZFiber (outer (js 0)) (left (js 2) 2) k a ≃
          TotalZFiber (outer (js 2)) (left (js 2) 2) k a :=
      { toFun := fun t ↦
          ⟨t.1, ⟨(hCommonZ (js 2) (js 0) t.1).trans t.2.1, t.2.2⟩⟩
        invFun := fun t ↦
          ⟨t.1, ⟨(hCommonZ (js 2) (js 0) t.1).symm.trans t.2.1, t.2.2⟩⟩
        left_inv := fun t ↦ by apply Subtype.ext; rfl
        right_inv := fun t ↦ by apply Subtype.ext; rfl }
    exact (Fintype.card_congr e).trans (hTotal (js 2) k a)
  have hCompat :=
    mme_dwz_table2_step1_fine_support_implies_grouped_compatibility
      (K := K) q m (outer (js 0))
      (fun i t ↦ left (js i) i t)
      (fun i t ↦ right (js i) i t)
      hCoarseMixed
      (fun t ↦ by simpa [retainedFineAddress] using hSupported t)
      (by
        intro s hs a
        exact hXSurvives (js 0) s hs a)
      (by
        intro s hs a
        simpa only [← hXY] using hYSurvives (js 1) s hs a)
      hTotalMixed
  simpa only [retainedFineCompatible, retainedFineAddress,
    fineSplitLeft_encode] using hCompat
