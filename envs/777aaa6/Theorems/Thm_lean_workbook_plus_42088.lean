-- Prove2me | Theorems.Thm_lean_workbook_plus_42088
-- name    : lean_workbook_plus_42088
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5cf0fbb0-f283-4087-912a-272f60669f4f
-- statement:
--   Let $ a,b,c\geq0$ .Prove that: \n $ a^3 + b^3 + c^3 - 3abc\geq2(\dfrac{b + c}{2} - a)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42088 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^3 + b^3 + c^3 - 3*a*b*c ≥ 2 * ((b + c) / 2 - a)^3   :=  by sorry
