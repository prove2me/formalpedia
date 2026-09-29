-- Prove2me | Theorems.Thm_lean_workbook_plus_37935
-- name    : lean_workbook_plus_37935
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6637caec-c4b0-49cd-854a-d7f7e17fee4c
-- statement:
--   Prove that $ x\mapsto x^a+a^x $ is increasing on $ [0,\infty) $ for $ a\ge 1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37935 (a : ℝ) (ha : 1 ≤ a) : ∀ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x ≤ y → x^a + a^x ≤ y^a + a^y   :=  by sorry
