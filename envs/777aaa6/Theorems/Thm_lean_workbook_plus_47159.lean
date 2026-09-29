-- Prove2me | Theorems.Thm_lean_workbook_plus_47159
-- name    : lean_workbook_plus_47159
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c82a7246-b1aa-43ef-bdac-9cea56be7816
-- statement:
--   Let $a,b,c>0.$ Prove that $$(a^2+b^2)(b^2+c^2)(c^2+a^2) \geq (a^2+bc)(b^2+ca)(c^2+ab)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47159 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)   :=  by sorry
