-- Prove2me | Theorems.Thm_lean_workbook_plus_66192
-- name    : lean_workbook_plus_66192
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/01a6a401-7556-4849-863f-70db96e0f6d6
-- statement:
--   Prove that $a^3+b^3+c^3\geq ab+bc+ac$ given $a,b,c$ are positive real numbers such that $abc\geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66192 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c ≥ 1) :
  a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b + b * c + c * a   :=  by sorry
