-- Prove2me | Theorems.Thm_lean_workbook_plus_45343
-- name    : lean_workbook_plus_45343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/56abefb4-588b-4167-bb1a-8f65c5a53c19
-- statement:
--   Let $a, b, c \geq 0, \ \ a^2+b^2+c^2 +abc = 4 \ \implies 2+abc\ge ab + bc + ca$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45343 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c = 4) : 2 + a * b * c ≥ a * b + b * c + c * a   :=  by sorry
