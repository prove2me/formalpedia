-- Prove2me | Theorems.Thm_lean_workbook_plus_11657
-- name    : lean_workbook_plus_11657
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/702d3086-da05-4f95-8ff2-bc1c24826bd9
-- statement:
--   The solution to the inequality $-3(c + 1)(c - \frac{13}{3}) \geq 0$ is $-1 \leq c \leq \frac{13}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11657 (c : ℝ) : -3 * (c + 1) * (c - 13/3) ≥ 0 ↔ -1 ≤ c ∧ c ≤ 13/3   :=  by sorry
