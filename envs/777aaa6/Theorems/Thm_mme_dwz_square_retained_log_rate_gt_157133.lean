-- Prove2me | Theorems.Thm_mme_dwz_square_retained_log_rate_gt_157133
-- name    : mme_dwz_square_retained_log_rate_gt_157133
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T09:57:22.636381+00:00
-- url     : https://prove2.me/theorems/6cbfa1f4-de31-49a0-9846-11d5517c5e4b
-- title:
--   DWZ Table 2: the retained-copy logarithmic rate exceeds 1.57133
-- statement:
--   For the exact $q=6$ distribution and split data from Duan--Wu--Zhou Table 2, let $R_{\mathrm{ret}}$ be the base-two logarithm of the retained-copy factor in Equation (25). Then
--
--   $$
--   R_{\mathrm{ret}}>\frac{157133}{100000}=1.57133.
--   $$
--
--   The retained rate is the minimum of the same-marginal entropy branch and the compatibility branch. The certificate therefore verifies both branches, including the constrained entropy supremum and the closed compatibility exponent from Lemma 6.7.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Lemma 6.7, Equation (25), Algorithm 2, Section 6.3 and Table 2 (printed pp. 55, 58-59); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_dwz_table2_entropy_potential
import Theorems.Thm_mme_modern_entropyBits_additive_certificate
open MME.DWZSquare

theorem mme_dwz_square_retained_log_rate_gt_157133 :
    (157133 / 100000 : ℝ) < retainedLogRate := by sorry
