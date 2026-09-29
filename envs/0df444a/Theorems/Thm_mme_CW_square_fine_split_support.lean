-- Prove2me | Theorems.Thm_mme_CW_square_fine_split_support
-- name    : mme_CW_square_fine_split_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:35:40.926927+00:00
-- url     : https://prove2.me/theorems/0015b1ac-f8fd-44bd-90aa-880a31c5b659
-- title:
--   Fine blocks of the squared Coppersmith--Winograd tensor satisfy both half-support equations
-- statement:
--   Give $CW_q^{\otimes 2}$ the product of the canonical three-gradings on its two level-one factors. If a fine homogeneous block indexed by left grades $\ell_0,\ell_1,\ell_2$ and right grades $r_0,r_1,r_2$ is nonzero, then
--
--   $$
--   \ell_0+\ell_1+\ell_2=2
--   \qquad\text{and}\qquad
--   r_0+r_1+r_2=2.
--   $$
--
--   This lifts the one-copy support equation to both halves of the square. It is the exact pointwise constraint used by Additional Zeroing-Out Step 1 to recover the missing third-mode split histogram from the surviving first- and second-mode histograms.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.1, Claim 6.2 and Additional Zeroing-Out Step 1. https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_CW_three_canonical_support

open MME
open MME.DWZStep1Support

universe u

set_option autoImplicit false

theorem mme_CW_square_fine_split_support
    (K : Type u) [Field K] (q : ℕ)
    (left right : Fin 3 → Fin 3)
    (h : (cwSquareFineSplitGrading K q).blockTensor
      (fun s => fineSplitGrade (left s) (right s)) ≠ 0) :
    ((left 0).val + (left 1).val + (left 2).val = 2) ∧
      ((right 0).val + (right 1).val + (right 2).val = 2) := by
  sorry
