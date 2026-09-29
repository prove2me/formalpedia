-- Prove2me | Theorems.Thm_lean_workbook_plus_6933
-- name    : lean_workbook_plus_6933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ab57f246-d011-4195-8655-a7554436012b
-- statement:
--   prove that \n\n $\frac{c^2}{d}+d\ge 2c$ \n\n given $c,d>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6933 : ∀ c d : ℝ, c > 0 ∧ d > 0 → c^2 / d + d ≥ 2 * c   :=  by sorry
