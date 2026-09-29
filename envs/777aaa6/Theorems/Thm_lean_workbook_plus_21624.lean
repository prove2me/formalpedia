-- Prove2me | Theorems.Thm_lean_workbook_plus_21624
-- name    : lean_workbook_plus_21624
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/74cdedf1-f25e-4154-8a4a-c3d83a98b7a0
-- statement:
--   Prove that $\frac{bc}{b^5+c^5+bc}+\frac{ca}{c^5+a^5+ca}+\frac{ab}{a^5+b^5+ab}\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21624 : ∀ a b c : ℝ, (b * c) / (b ^ 5 + c ^ 5 + b * c) + (c * a) / (c ^ 5 + a ^ 5 + c * a) + (a * b) / (a ^ 5 + b ^ 5 + a * b) ≤ 1   :=  by sorry
