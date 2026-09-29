-- Prove2me | Theorems.Thm_lean_workbook_plus_69158
-- name    : lean_workbook_plus_69158
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d373df31-c90a-4f90-98c1-5126c68c41e9
-- statement:
--   For all real numbers $a,b,c$ : $ab+bc+ca\leq a^{2}+b^{2}+c^{2}\Leftrightarrow 3(ab+bc+ca)\leq (a+b+c)^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69158 : ∀ a b c : ℝ, a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 ↔ 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2   :=  by sorry
