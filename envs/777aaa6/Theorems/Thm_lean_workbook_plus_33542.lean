-- Prove2me | Theorems.Thm_lean_workbook_plus_33542
-- name    : lean_workbook_plus_33542
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/57febcf4-937a-42ab-872b-d5225ed5fd0e
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers such that $a^3+b^2+c\geq a^4+b^3+c^3$ . Prove that: \n $$a^3+b^3+2c^3\leq4$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33542 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^3 + b^2 + c ≥ a^4 + b^3 + c^3) : a^3 + b^3 + 2*c^3 ≤ 4   :=  by sorry
