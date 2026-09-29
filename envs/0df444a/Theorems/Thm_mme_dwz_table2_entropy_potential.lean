-- Prove2me | Theorems.Thm_mme_dwz_table2_entropy_potential
-- name    : mme_dwz_table2_entropy_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:48:16.896921+00:00
-- url     : https://prove2.me/theorems/3cf36d1b-5316-46a4-a44c-8a8177fd5541
-- title:
--   Table 2: certified additive potentials for same-marginal entropy
-- statement:
--   Check the fifteen explicit logarithmic residuals for the rational
--   additive potentials stored with the Table 2 data. Their common error bound is
--   4e-6 bits. Together with the already-proved additive-potential entropy theorem,
--   this bounds Algorithm 2's same-marginal maximum without trusting a floating-
--   point optimizer.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Algorithm 2 and Table 2 (printed pp. 58-59); additive-potential certification is a formal verification device.

import Definitions.Def_mme_dwz_square_data
open MME.DWZSquare

theorem mme_dwz_table2_entropy_potential (s : Fin 15) :
    |Real.log (alpha s) / Real.log 2 -
      (entropyLambdaZero + entropyLambdaX (shapeX s) +
        entropyLambdaY (shapeY s) + entropyLambdaZ (shapeZ s))| ≤
      entropyEpsilon := by sorry
