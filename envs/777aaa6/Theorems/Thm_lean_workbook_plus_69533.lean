-- Prove2me | Theorems.Thm_lean_workbook_plus_69533
-- name    : lean_workbook_plus_69533
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/452a29d6-e000-4b57-8481-85ef8dbe9265
-- statement:
--   For $ a,b,c>0 $ prove that:\n$ \sum{a^4}+\sum{a^2b^2}\geq\sum{a^3b}+\sum{ab^3}. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69533 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^4 + b^4 + c^4 + a^2 * b^2 + a^2 * c^2 + b^2 * c^2 ≥ a^3 * b + b^3 * a + a^3 * c + c^3 * a + b^3 * c + c^3 * b   :=  by sorry
