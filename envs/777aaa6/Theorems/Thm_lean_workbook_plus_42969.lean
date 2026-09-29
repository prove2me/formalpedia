-- Prove2me | Theorems.Thm_lean_workbook_plus_42969
-- name    : lean_workbook_plus_42969
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/9d172c11-d8aa-42bc-a6af-e6ce754ca80d
-- statement:
--   $\sum_{cyc}(a^4+a^2b^2-2a^3b)\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42969 (a b c : ℝ) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - 2 * a^3 * b - 2 * b^3 * c - 2 * c^3 * a ≥ 0   :=  by sorry
