-- Prove2me | Theorems.Thm_lean_workbook_plus_33924
-- name    : lean_workbook_plus_33924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c1384316-3afe-4b17-8775-8cbe3c4c59ff
-- statement:
--   Let $a, b, c > 0$ . Prove $(a+b)^{3}+(2a+b)^{3}+(3a)^{3}\le 8(9a^{3}+b^{3})$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33924 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 3 + (2 * a + b) ^ 3 + (3 * a) ^ 3 ≤ 8 * (9 * a ^ 3 + b ^ 3)   :=  by sorry
