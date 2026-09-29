-- Prove2me | Theorems.Thm_lean_workbook_plus_46338
-- name    : lean_workbook_plus_46338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ab3173db-715f-4289-acd4-366728958b30
-- statement:
--   Let $ a,b $ be positive real numbers. Prove that $ 2(a^4+b^4)+17>16ab $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46338 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 2 * (a ^ 4 + b ^ 4) + 17 > 16 * a * b   :=  by sorry
