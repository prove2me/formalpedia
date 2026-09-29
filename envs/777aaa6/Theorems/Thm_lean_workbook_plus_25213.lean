-- Prove2me | Theorems.Thm_lean_workbook_plus_25213
-- name    : lean_workbook_plus_25213
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d275d6e8-8c72-4978-8022-bd5d62769959
-- statement:
--   Prove that if $ a > 1$ then $ \frac {1}{a - 1} + \frac {1}{a} + \frac {1}{a + 1} > \frac {3}{a}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25213 (a : ℝ) (h : a > 1) : 1 / (a - 1) + 1 / a + 1 / (a + 1) > 3 / a   :=  by sorry
