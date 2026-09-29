-- Prove2me | Theorems.Thm_lean_workbook_plus_63823
-- name    : lean_workbook_plus_63823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5fcbced6-a340-4bb5-8577-d98b14aa2a32
-- statement:
--   Prove that $a^{2}+b^{2}+c^{2}-ab-bc-ca \geq 2(a-b)(a-c)$ for $c \geq a \geq b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63823 (a b c : ℝ) (h : c ≥ a ∧ a ≥ b) : a^2 + b^2 + c^2 - a * b - b * c - c * a ≥ 2 * (a - b) * (a - c)   :=  by sorry
