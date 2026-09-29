-- Prove2me | Theorems.Thm_lean_workbook_plus_23447
-- name    : lean_workbook_plus_23447
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/85de2896-9eec-479f-9ee7-5db6cac1ddfd
-- statement:
--   For $ a,b,c\ge 0 $ prove that:\n $ 7(a^2+b^2+c^2)+a^2b+b^2c+c^2a+27\ge 17(a+b+c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23447 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 7 * (a ^ 2 + b ^ 2 + c ^ 2) + a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + 27 ≥ 17 * (a + b + c)   :=  by sorry
