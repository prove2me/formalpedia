-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_source_mixed_zero_of_coordinate
-- name    : mme_dwz_step1_filtered_source_mixed_zero_of_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:42:15.53679+00:00
-- url     : https://prove2.me/theorems/c6127850-a8e4-451d-90af-bf333950aff7
-- title:
--   A zero canonical coordinate kills the Step-1 mixed source map
-- statement:
--   Fix a mixed triple of broken square-CW address tensors and suppose that its canonical square block vanishes at one coordinate. Then the complete tensor map obtained from the three Step-1 filtered broken-source maps is zero:
--
--   $$T_{a_X(r),a_Y(r),a_Z(r)}=0\quad\Longrightarrow\quad\operatorname{map}(f_X,f_Y,f_Z)\bigl((\mathrm{CW}_6\otimes\mathrm{CW}_6)^{\otimes N}\bigr)=0.$$
--
--   The result is stable under all broken-address postprocessing because graded-address projection factors coordinatewise through the zero block.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_source_mixed_zero_of_coordinate
    {K : Type u} [Field K] {k m N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (copy : ∀ j : Fin k, DWZSquare.BrokenBlockCopy
      (DWZTable2StandardForm.UsefulBlock m (outer j)))
    (js : Fin 3 → Fin k) (r : Fin N)
    (hrzero :
      (cwSquareCanonicalGrading K 6).blockTensor
        (fun i ↦ coarseAddress (outer (js i)) i r) = 0) :
    PiTensorProduct.map
        (fun i ↦ step1FilteredBrokenSourceMaps K m
          (outer (js i)) (copy (js i)) i)
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow N).t = 0 := by
  sorry
