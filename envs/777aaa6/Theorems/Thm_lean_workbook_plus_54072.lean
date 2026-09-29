-- Prove2me | Theorems.Thm_lean_workbook_plus_54072
-- name    : lean_workbook_plus_54072
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/38bccb87-46fd-416c-8a39-3ef663326cee
-- statement:
--   Let $a, b$ be non-negative real numbers. Prove that $(a+b+1)^4 \ge (a^2-a+1)(b^2-b+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54072 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b + 1) ^ 4 ≥ (a ^ 2 - a + 1) * (b ^ 2 - b + 1)   :=  by sorry
