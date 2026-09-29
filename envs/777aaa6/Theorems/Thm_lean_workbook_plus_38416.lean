-- Prove2me | Theorems.Thm_lean_workbook_plus_38416
-- name    : lean_workbook_plus_38416
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/91553f62-1f30-44db-bd64-26ffb10e0c9c
-- statement:
--   Given the same conditions, prove that $|b - c| < a$, $|c - a| < b$, and $|a - b| < c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38416 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : |b - c| < a ∧ |c - a| < b ∧ |a - b| < c   :=  by sorry
