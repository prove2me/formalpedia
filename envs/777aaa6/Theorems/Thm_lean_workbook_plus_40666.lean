-- Prove2me | Theorems.Thm_lean_workbook_plus_40666
-- name    : lean_workbook_plus_40666
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6fe3b698-6437-4753-b970-3fd6ab42758a
-- statement:
--   Prove that if $a^5 - a^3 + a = 2$ and $a > 0$, then $3 < a^3 < 4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40666 (a : ℝ) (ha : 0 < a) (h : a^5 - a^3 + a = 2) : 3 < a^3 ∧ a^3 < 4   :=  by sorry
