-- Prove2me | Theorems.Thm_lean_workbook_plus_72864
-- name    : lean_workbook_plus_72864
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f10aac6d-6786-4d00-8511-d63422df37ed
-- statement:
--   Prove that: $\frac{a^3}{(a+b)^2}+\frac{b^3}{(b+c)^2}+\frac{c^3}{(c+a)^2}\geq \frac{a+b+c}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72864 : ∀ a b c : ℝ, (a^3 / (a + b) ^ 2 + b^3 / (b + c) ^ 2 + c^3 / (c + a) ^ 2) ≥ (a + b + c) / 4   :=  by sorry
