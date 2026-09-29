-- Prove2me | Theorems.Thm_lean_workbook_plus_38306
-- name    : lean_workbook_plus_38306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d19ae91a-3e15-4d6b-bc9d-635dd386b11a
-- statement:
--   Let $a,b,c>0$ and $ab+bc+ca=1$ .Prove that $$(a^2+bc)(b^2+ca)(c^2+ab)+ a^2b^2c^2\geq \frac{1}{3}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38306 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) + a^2 * b^2 * c^2 ≥ 1 / 3   :=  by sorry
