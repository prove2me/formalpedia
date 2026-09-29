-- Prove2me | Theorems.Thm_lean_workbook_plus_42556
-- name    : lean_workbook_plus_42556
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/4c4d3ecf-3200-43cd-909e-0106534c0738
-- statement:
--   Given $c \geq b \geq a \geq 0$, prove that $(a+3b)(b+4c)(c+2a) \geq 60abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42556 (a b c : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
