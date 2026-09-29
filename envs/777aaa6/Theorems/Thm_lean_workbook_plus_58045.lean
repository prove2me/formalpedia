-- Prove2me | Theorems.Thm_lean_workbook_plus_58045
-- name    : lean_workbook_plus_58045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/72a81a55-b736-4930-94d8-8292ea217755
-- statement:
--   From the sum, $\frac{a}r+a+ar = 5 \implies a\left(\frac{1}r+r+1\right) = 5$ $ (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58045 (a r : ℝ) : a / r + a + a * r = 5 → a * (1 / r + r + 1) = 5   :=  by sorry
