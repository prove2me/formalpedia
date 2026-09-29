-- Prove2me | Theorems.Thm_lean_workbook_plus_24509
-- name    : lean_workbook_plus_24509
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/cc34ef08-2ef9-4859-b15c-992e2fe37c02
-- statement:
--   Show that $x^{\frac1x}\leq x^x$ for $x>1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24509 (x : ℝ) (hx : 1 < x) : x^(1/x) ≤ x^x   :=  by sorry
