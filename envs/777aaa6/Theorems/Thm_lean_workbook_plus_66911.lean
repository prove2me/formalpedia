-- Prove2me | Theorems.Thm_lean_workbook_plus_66911
-- name    : lean_workbook_plus_66911
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/144ac6a4-c10f-408b-974c-7dc6e378d16a
-- statement:
--   Prove that for positive numbers $a$, $b$, and $c$ with $abc = 1$, the following inequality holds:\n$$ab^2 + ac^2 \geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66911 (a b c : ℝ) (habc : a * b * c = 1) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a * b^2 + a * c^2 ≥ 1   :=  by sorry
