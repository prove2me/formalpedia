-- Prove2me | Theorems.Thm_lean_workbook_plus_2428
-- name    : lean_workbook_plus_2428
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e2596223-87a6-4862-b67f-064c2f13531b
-- statement:
--   Let $a$ and $b$ be two positive real numbers with $a \le 2b \le 3a.$ Prove that $a^2+ b^2\le \frac{5}{2} ab$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2428 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 2 * b) (h : 2 * b ≤ 3 * a) : a^2 + b^2 ≤ 5 / 2 * a * b   :=  by sorry
