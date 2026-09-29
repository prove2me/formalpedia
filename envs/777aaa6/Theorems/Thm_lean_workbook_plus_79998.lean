-- Prove2me | Theorems.Thm_lean_workbook_plus_79998
-- name    : lean_workbook_plus_79998
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/5924b96e-1f1f-4497-8d22-716390563b31
-- statement:
--   Prove that \(\sin^4(x) = \frac{3}{8} - \frac{4}{8} \cos(2x) + \frac{1}{8} \cos(4x)\) for all \(x\) in the domain of sine.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79998 (x : ℝ) : (sin x)^4 = 3/8 - 4/8 * cos (2 * x) + 1/8 * cos (4 * x)   :=  by sorry
