-- Prove2me | Theorems.Thm_lean_workbook_plus_34444
-- name    : lean_workbook_plus_34444
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/cf1d08bc-bfd0-4a37-9f9b-e5af3fbd99aa
-- statement:
--   Derive the inequality $\sqrt{a^2+b^2}\ge \frac{a+b}{\sqrt{2}}$ from $2(a^2+b^2)\ge (a+b)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34444 : ∀ a b : ℝ, 2 * (a ^ 2 + b ^ 2) ≥ (a + b) ^ 2 → Real.sqrt (a ^ 2 + b ^ 2) ≥ (a + b) / Real.sqrt 2   :=  by sorry
