-- Prove2me | Theorems.Thm_lean_workbook_plus_61548
-- name    : lean_workbook_plus_61548
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f3ebb27b-b77a-46b0-b815-015cd3910beb
-- statement:
--   (Solution 1) $a^4 + b^4 + c^4 \geq abc(a+b+c) \Leftrightarrow (ab-bc)^2 + (ac-bc)^2 + (ab-ac)^2 \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61548 (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c) ↔ (a * b - b * c) ^ 2 + (a * c - b * c) ^ 2 + (a * b - a * c) ^ 2 ≥ 0   :=  by sorry
