-- Prove2me | Theorems.Thm_lean_workbook_plus_20810
-- name    : lean_workbook_plus_20810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9073eb88-1a16-4710-a3e6-7f73b88ec97b
-- statement:
--   Prove that \n $4(ab+bc+ca)(b^2+bc+c^2)\le (b+c)^2(a+b+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20810 : ∀ a b c : ℝ, 4 * (a * b + b * c + c * a) * (b ^ 2 + b * c + c ^ 2) ≤ (b + c) ^ 2 * (a + b + c) ^ 2   :=  by sorry
