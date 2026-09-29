-- Prove2me | Theorems.Thm_lean_workbook_plus_47791
-- name    : lean_workbook_plus_47791
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/35ad58e1-6011-406f-8fa2-fe969865a033
-- statement:
--   if a,b,c>o, prove that $ a^3/(b+c) + b^3/(a+c) + c^3/(a+b)\geq(a^2+b^2+c^2)/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47791 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a^3 / (b + c) + b^3 / (a + c) + c^3 / (a + b) ≥ (a^2 + b^2 + c^2) / 2   :=  by sorry
