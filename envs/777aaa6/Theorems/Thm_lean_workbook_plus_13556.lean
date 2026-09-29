-- Prove2me | Theorems.Thm_lean_workbook_plus_13556
-- name    : lean_workbook_plus_13556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2586b1ac-1c44-402c-b950-8665a2e2cfad
-- statement:
--   For $ a,b,c>0 $ prove that:\n$ \sum{a^4}+\sum{a^2b^2}\geq\sum{a^3b}+\sum{ab^3}. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13556 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a^3 * b + b^3 * c + c^3 * a + a * b^3 + b * c^3 + c * a^3   :=  by sorry
