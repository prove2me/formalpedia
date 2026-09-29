-- Prove2me | Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
-- name    : mme_CW_square_canonical_support_and_scalar_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:21.986426+00:00
-- url     : https://prove2.me/theorems/6c466fa1-ca20-45aa-b621-444ed87a72aa
-- title:
--   Support and scalar fields of the canonical CW-square five-grading
-- statement:
--   Let $T_q$ be the Coppersmith--Winograd tensor and equip $T_q\otimes T_q$ with its canonical five-grading by coordinate-pair degree. Every nonzero graded constituent has total degree four, and the three extreme constituents are scalar matrix-multiplication tensors:
--
--   $$
--   T_{IJK}=0\quad(I+J+K\ne4),\qquad T_{004},T_{040},T_{400}\ge\langle1,1,1\rangle.
--   $$
--
--   These are the support and scalar fields in the standard fifteen-constituent decomposition of the CW square. Every block here is taken from the same fixed public grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, decomposition of the square into fifteen total-degree-four constituents.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_support_and_scalar_blocks
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) := by sorry
