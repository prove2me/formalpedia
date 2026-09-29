-- Prove2me | Theorems.Thm_lean_workbook_plus_58036
-- name    : lean_workbook_plus_58036
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/28c27a8b-d12e-4ada-a33a-3ddfc7363db2
-- statement:
--   Prove that $ \displaystyle \left ( 1 + \frac{1}{1^3} \right ) \left ( 1 + \frac{1}{2^3} \right ) \left ( 1 + \frac{1}{3^3} \right ) + \dots + \left(1 + \frac{1}{N^3} \right ) < 3 - \frac{1}{N}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58036 : ∀ N : ℕ, (∑ i in Finset.Icc 1 N, (1 + 1 / i ^ 3)) < 3 - 1 / N   :=  by sorry
