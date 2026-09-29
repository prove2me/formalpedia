-- Prove2me | Theorems.Thm_lean_workbook_plus_56566
-- name    : lean_workbook_plus_56566
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6da93ba9-66b9-45b8-8abb-47dc86d44741
-- statement:
--   Prove that for positive real numbers a, b, and c, the inequality $2(a^3 + b^3 + c^3) \geq a^2(b+c) + b^2(c+a) +c^2(b+a)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56566 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^3 + b^3 + c^3) ≥ a^2 * (b + c) + b^2 * (c + a) + c^2 * (b + a)   :=  by sorry
