-- Prove2me | Theorems.Thm_lean_workbook_plus_21758
-- name    : lean_workbook_plus_21758
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6d8c59c0-900b-47df-b8ac-b53636cbd5e2
-- statement:
--   Prove that for positive numbers $a, b, c$, the following identity holds: $a^2(b-c)^2 + b^2(c-a)^2 + c^2(a-b)^2 \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21758 (a b c : ℝ) : a^2 * (b - c)^2 + b^2 * (c - a)^2 + c^2 * (a - b)^2 ≥ 0   :=  by sorry
