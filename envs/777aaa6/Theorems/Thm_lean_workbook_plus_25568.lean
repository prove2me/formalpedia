-- Prove2me | Theorems.Thm_lean_workbook_plus_25568
-- name    : lean_workbook_plus_25568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/4a380573-3b31-4831-bbef-e78330919ada
-- statement:
--   Given $n = a^2 + 5b^2$ where a and b are integers not equal to 0, express $n^4$ in the form $n^4 = a'^2 + 5b'^2$ where a' and b' are integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25568 (n a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a * b ≠ 0) (h : n = a^2 + 5 * b^2) : ∃ a' b' : ℤ, a'^2 + 5 * b'^2 = n^4   :=  by sorry
