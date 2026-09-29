-- Prove2me | Theorems.Thm_lean_workbook_plus_38510
-- name    : lean_workbook_plus_38510
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b3712e30-2e45-44b5-a448-5bd258caa68c
-- statement:
--   Prove the inequality\n\n$ \sqrt {a^2 + (1 - b)^2} + \sqrt { b^2 (1 - c)^2} + \sqrt {c^2 + (1 - a)^2} \ge \frac { 3 \sqrt {2}}{2}$\n\nholds for arbitrary real numbers $ a,b,c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38510 : ∀ a b c : ℝ, (Real.sqrt (a ^ 2 + (1 - b) ^ 2) + Real.sqrt (b ^ 2 * (1 - c) ^ 2) + Real.sqrt (c ^ 2 + (1 - a) ^ 2)) ≥ (3 * Real.sqrt 2) / 2   :=  by sorry
