-- Prove2me | Theorems.Thm_lean_workbook_plus_67558
-- name    : lean_workbook_plus_67558
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3637249e-8d0f-40c5-974d-ad3bf7779f42
-- statement:
--   Let $a$ and $b$ be two positive real numbers with $a \le 2b \le 4a$ . Prove that $4ab \le2 (a^2+ b^2) \le 5 ab$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67558 (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 2 * b) (h3 : 2 * b ≤ 4 * a) :
  4 * a * b ≤ 2 * (a ^ 2 + b ^ 2) ∧ 2 * (a ^ 2 + b ^ 2) ≤ 5 * a * b   :=  by sorry
