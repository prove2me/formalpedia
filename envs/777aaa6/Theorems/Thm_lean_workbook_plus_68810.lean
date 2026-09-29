-- Prove2me | Theorems.Thm_lean_workbook_plus_68810
-- name    : lean_workbook_plus_68810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/dc7aa265-5dbc-432e-85d9-365fd2eab3ca
-- statement:
--   For nonnegative numbers, $a$ , $b$ , $c$ , show that $3(a^3+b^3+c^3)\geq(a+b+c)(a^2+b^2+c^2)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68810 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 3 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
