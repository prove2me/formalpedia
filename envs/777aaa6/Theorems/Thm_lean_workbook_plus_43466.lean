-- Prove2me | Theorems.Thm_lean_workbook_plus_43466
-- name    : lean_workbook_plus_43466
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a2f0f0f0-b9d6-4389-a6df-7e8ede4fe4e1
-- statement:
--   Prove that if $a\geq b\geq c > 0$ and $a+b+c = 1$, then $\frac{b}{b+c}+\frac{c}{c+a}+\frac{a}{a+b} \ge \frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43466 (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c > 0 ∧ a + b + c = 1) :
  b / (b + c) + c / (c + a) + a / (a + b) ≥ 3 / 2   :=  by sorry
