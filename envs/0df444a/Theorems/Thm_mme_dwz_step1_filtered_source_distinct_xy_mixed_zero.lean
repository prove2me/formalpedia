-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_source_distinct_xy_mixed_zero
-- name    : mme_dwz_step1_filtered_source_distinct_xy_mixed_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:42:40.026516+00:00
-- url     : https://prove2.me/theorems/ea2acd0a-b1c7-438f-997b-039a84e938a5
-- title:
--   A distinct X/Y owner pair has zero Step-1 mixed tensor map
-- statement:
--   Let a family of broken square-CW address tensors be equipped with the Step-1 X/Y filters. Assume that every coordinatewise-supported mixed triple has the same X and Y owner. Then any mixed triple with distinct X and Y owners has zero tensor map:
--
--   $$j_X\ne j_Y\quad\Longrightarrow\quad\operatorname{map}(f_{j_X}^{X},f_{j_Y}^{Y},f_{j_Z}^{Z})\bigl((\mathrm{CW}_6\otimes\mathrm{CW}_6)^{\otimes N}\bigr)=0.$$
--
--   Indeed, distinct X/Y owners force a zero canonical block at some coordinate, and this zero persists through all Step-1 broken-address postmaps.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME Module PiTensorProduct
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_source_distinct_xy_mixed_zero
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
  sorry
