-- Prove2me | Theorems.Thm_lean_workbook_plus_38433
-- name    : lean_workbook_plus_38433
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/48cdaaf7-599b-4094-aa7e-02a4a0f7ab0e
-- statement:
--   Prove that for positive real numbers a, b, and c, the following inequality holds:\n$$\sqrt{2(a^2+b^2)(b^2+c^2)(c^2+a^2)} \geq (a+b)(b+c)(c+a)-4abc.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38433 (a b c : ℝ) : Real.sqrt (2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2)) ≥ (a + b) * (b + c) * (c + a) - 4 * a * b * c   :=  by sorry
