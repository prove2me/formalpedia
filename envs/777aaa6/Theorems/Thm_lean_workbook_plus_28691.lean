-- Prove2me | Theorems.Thm_lean_workbook_plus_28691
-- name    : lean_workbook_plus_28691
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/331f6eb1-fab2-484e-981b-c4d1064071bc
-- statement:
--   Now: $a+b+c=7-d,a^{2}+b^{2}+c^{2}=13-d^{2}$ and it is well-known (e.g. by sums of squares) that $3\left(a^{2}+b^{2}+c^{2}\right)\geq\left(a+b+c\right)^{2}$ for all $a,b,c\in\mathbb{R}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28691  (a b c d : ℝ)
  (h₀ : a + b + c = 7 - d)
  (h₁ : a^2 + b^2 + c^2 = 13 - d^2) :
  3 * (a^2 + b^2 + c^2) ≥ (a + b + c)^2   :=  by sorry
