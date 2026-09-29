-- Prove2me | Theorems.Thm_lean_workbook_plus_24926
-- name    : lean_workbook_plus_24926
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/176dfd2d-5a82-43a9-83fb-8f63c0fd4c61
-- statement:
--   Let $ a,b, c>0$ . Prove that \n $$\frac{a^2+b^2}{a+b}+\frac{b^2+c^2}{b+c}\geq \frac{a+2b+c}{2}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24926 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 + b^2) / (a + b) + (b^2 + c^2) / (b + c) ≥ (a + 2 * b + c) / 2   :=  by sorry
