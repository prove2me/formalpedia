-- Prove2me | Theorems.Thm_lean_workbook_plus_29710
-- name    : lean_workbook_plus_29710
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/eb2cf415-5ccc-48e9-b983-6cb84022d6a6
-- statement:
--   Either $\sqrt{b^2-4ac}\le |b|-2$ and so $|b|\ge 2$ and $-4ac\le -4|b|+4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29710 (a b c : ℝ) (h : 0 < a) (h2 : 0 < c) : (Real.sqrt (b ^ 2 - 4 * a * c) ≤ |b| - 2 → |b| ≥ 2 ∧ -4 * a * c ≤ -4 * |b| + 4)   :=  by sorry
