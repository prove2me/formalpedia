-- Prove2me | Theorems.Thm_mme_dwz_positive_332_branch_lower_bounds
-- name    : mme_dwz_positive_332_branch_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:36:54.866559+00:00
-- url     : https://prove2.me/theorems/d398b1ae-2bf4-4974-a295-26b583f81352
-- title:
--   Positive component 332: certified branch lower bounds
-- statement:
--   For the concrete six-region fine profile of the DWZ $(3,3,2)$ component, each of the three branches of the explicit entropy rate is bounded below by its rational certificate value: the coarse branch (coarse entropy minus the witness-entropy penalty) by `coarseLower - penaltyUpper`, and the two parent-word branches (joint word entropy minus boundary/interior compatibility entropy) by `parentLower - compatibilityUpper`. Every entropy term is bounded by the certified logarithm intervals.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-166 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_332_entropy_certificate_data
import Theorems.Thm_mme_dwz_positive_332_log_intervals

open BigOperators MME MME.RecursiveYZ MME.DWZ332Fine MME.DWZ332Certificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem mme_dwz_positive_332_branch_lower_bounds :
    ((coarseLower : ℝ) - penaltyUpper ≤ coarseRate - penaltyRate) ∧
    ((parentLower 1 : ℝ) - compatibilityUpper 0 ≤ parentRate 1 - compatibilityRate 0) ∧
    ((parentLower 2 : ℝ) - compatibilityUpper 1 ≤ parentRate 2 - compatibilityRate 1) := by sorry
