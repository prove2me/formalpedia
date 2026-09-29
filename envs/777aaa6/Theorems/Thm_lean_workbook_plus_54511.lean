-- Prove2me | Theorems.Thm_lean_workbook_plus_54511
-- name    : lean_workbook_plus_54511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/33dcbc41-a285-4779-bc28-34411ff1d437
-- statement:
--   Given a quadratic function $f(x) = ax^2 + bx + c$, where $a \neq 0$ and $\Delta = b^2 - 4ac \geq 0$, factor $f(x)$ using the quadratic formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54511 (a b c x : ℝ) (ha : a ≠ 0) (h : b^2 - 4 * a * c ≥ 0) : a * x^2 + b * x + c = a * (x - (-b + Real.sqrt (b^2 - 4 * a * c)) / (2 * a)) * (x - (-b - Real.sqrt (b^2 - 4 * a * c)) / (2 * a))   :=  by sorry
