-- Prove2me | Theorems.Thm_lean_workbook_plus_31707
-- name    : lean_workbook_plus_31707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/828d428d-27dd-4604-b1f6-2f2c57e99473
-- statement:
--   assume , $ b \leq max(a,c)$ and $ b \geq min(a,c)$ \n $ = > a(b - a)(b - c) \leq 0 \iff a^2b + abc \geq ab^2 + ca^2 (1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31707  (a b c : ℝ)
  (h₀ : b ≤ max a c)
  (h₁ : b ≥ min a c) :
  a * (b - a) * (b - c) ≤ 0 ↔ a^2 * b + a * b * c ≥ a * b^2 + c * a^2   :=  by sorry
