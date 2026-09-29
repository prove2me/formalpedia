-- Prove2me | Theorems.Thm_lean_workbook_plus_17840
-- name    : lean_workbook_plus_17840
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/04e2c364-8dea-4150-a55c-8c55ee969cd1
-- statement:
--   Prove the inequality\n\n$\frac{a^2+16bc}{b^2+c^2}+\frac{b^2+16ca}{c^2+a^2}+\frac{c^2+16ab}{a^2+b^2} \ge 10$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17840 :  ∀ a b c : ℝ, (a^2 + 16 * b * c) / (b^2 + c^2) + (b^2 + 16 * c * a) / (c^2 + a^2) + (c^2 + 16 * a * b) / (a^2 + b^2) ≥ 10   :=  by sorry
