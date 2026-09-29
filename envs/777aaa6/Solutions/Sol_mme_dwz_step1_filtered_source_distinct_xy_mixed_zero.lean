-- Prove2me | solution 1 for mme_dwz_step1_filtered_source_distinct_xy_mixed_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:07:10.823932+00:00
-- url     : https://prove2.me/submissions/dec5374a-a239-4593-85d9-66a0acd81d82

import Theorems.Thm_mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
import Theorems.Thm_mme_dwz_step1_filtered_source_mixed_zero_of_coordinate

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress (outer (js i)) i r) ≠ 0) →
      js 0 = js 1)
    (js : Fin 3 → Fin k) (h01 : js 0 ≠ js 1) :
    PiTensorProduct.map
        (fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0 := by
  obtain ⟨r, hrzero⟩ :=
    mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
      (K := K) outer hXYOwner js h01
  exact mme_dwz_step1_filtered_source_mixed_zero_of_coordinate
    (K := K) outer copy js r hrzero
