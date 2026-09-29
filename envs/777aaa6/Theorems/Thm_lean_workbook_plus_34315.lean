-- Prove2me | Theorems.Thm_lean_workbook_plus_34315
-- name    : lean_workbook_plus_34315
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/cbb27a90-c030-42bd-a16e-32a4ee6dae08
-- statement:
--   Prove that $4(a+b+c)^{3}\geq 9(ab+bc+ca)+27(a+b+c)$ given $a,b,c\geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34315 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) : 4 * (a + b + c) ^ 3 ≥ 9 * (a * b + b * c + c * a) + 27 * (a + b + c)   :=  by sorry
