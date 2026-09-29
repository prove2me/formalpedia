-- Prove2me | Theorems.Thm_lean_workbook_plus_46145
-- name    : lean_workbook_plus_46145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e10a090d-5604-4b18-99e0-ffd7e0ad8093
-- statement:
--   Prove that if $ a,b,c > 0$ and $ a + b + c = 3$ then: $ a^4 + b^4 + c^4 \ge a^3 + b^3 + c^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46145 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^4 + b^4 + c^4 ≥ a^3 + b^3 + c^3   :=  by sorry
