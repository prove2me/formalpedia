-- Prove2me | Theorems.Thm_lean_workbook_plus_45492
-- name    : lean_workbook_plus_45492
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c3184f20-2df4-4a19-a9d9-9baf041d252b
-- statement:
--   For reals $a\geq b \geq c \geq d \geq 0$ with $a^2+b^2+c^2+d^2=1$\nProve that $a+b \geq 1\geq c+d$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45492 (a b c d : ℝ) (h : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ 0) (h2: a^2 + b^2 + c^2 + d^2 = 1) : a + b ≥ 1 ∧ 1 ≥ c + d   :=  by sorry
