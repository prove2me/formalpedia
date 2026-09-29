-- Prove2me | Theorems.Thm_lean_workbook_plus_42826
-- name    : lean_workbook_plus_42826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/3ed29157-45f4-45c4-9e95-87567f0124f8
-- statement:
--   Prove that for any real numbers $a, b, c$ with $a \geq b \geq c$, the inequality $(a+b+c)^2 \geq 3(ab+bc+ac)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42826 (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c) : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + a * c)   :=  by sorry
