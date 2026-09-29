-- Prove2me | Theorems.Thm_mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
-- name    : mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T10:42:00.65055+00:00
-- url     : https://prove2.me/theorems/cc4ec09a-e472-41a3-9016-9eded4a192a3
-- title:
--   Distinct X/Y owners force a zero coarse coordinate block
-- statement:
--   Consider a mixed triple of canonical square-CW addresses. Assume that every triple whose canonical block is nonzero at every coordinate must use the same owner in the X and Y modes. Then a triple with distinct X and Y owners has some coordinate at which its canonical block vanishes:
--
--   $$j_X\ne j_Y\quad\Longrightarrow\quad\exists r,\;T_{a_X(r),a_Y(r),a_Z(r)}=0.$$
--
--   This is the logical owner-isolation step that exposes the coordinate used by Step-1 zeroing.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6, Additional Zeroing-Out Step 1; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_step1_broken_owner_maps

open MME
open MME.DWZSourceAligned

universe u

set_option autoImplicit false

theorem mme_dwz_step1_filtered_source_distinct_xy_exists_zero_coordinate
    {K : Type u} [Field K] {k N : ℕ}
    (outer : Fin k → Fin N → Fin 15)
    (hXYOwner : ∀ js : Fin 3 → Fin k,
      (∀ r : Fin N,
        (cwSquareCanonicalGrading K 6).blockTensor
          (fun i ↦ coarseAddress (outer (js i)) i r) ≠ 0) →
      js 0 = js 1)
    (js : Fin 3 → Fin k) (h01 : js 0 ≠ js 1) :
    ∃ r : Fin N,
      (cwSquareCanonicalGrading K 6).blockTensor
        (fun i ↦ coarseAddress (outer (js i)) i r) = 0 := by
  sorry
