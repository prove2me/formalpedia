-- Prove2me | Theorems.Thm_lean_workbook_plus_78674
-- name    : lean_workbook_plus_78674
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f69493b0-c76c-4358-baca-b7ca2ee37df3
-- statement:
--   $\sin{x}-\sin{y}=2\cos{\frac{x+y}{2}}\sin{\frac{x-y}{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78674 (x y : ℝ) : sin x - sin y = 2 * cos ((x + y) / 2) * sin ((x - y) / 2)   :=  by sorry
