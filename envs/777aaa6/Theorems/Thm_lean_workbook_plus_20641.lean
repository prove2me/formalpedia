-- Prove2me | Theorems.Thm_lean_workbook_plus_20641
-- name    : lean_workbook_plus_20641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fb31a86a-c3b5-4014-9636-7f74c0c372d1
-- statement:
--   Assume $a\geq b\geq c$, then $a-b\geq 0$ and $b-c\geq 0$, then $(a-b)(b-c)\geq 0$, but $c-a\leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20641 (a b c : ℝ) (h₁ : a ≥ b) (h₂ : b ≥ c) : (a - b) * (b - c) ≥ 0 ∧ c - a ≤ 0   :=  by sorry
