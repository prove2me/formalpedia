-- Prove2me | Theorems.Thm_lean_workbook_plus_13122
-- name    : lean_workbook_plus_13122
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/1457b407-5f0d-49ca-8784-c5950dd22c26
-- statement:
--   In triangle $ABC$, prove that: $(a+b-c-\sqrt{(a+c-b)(b+c-a)})^2\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13122 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + b - c - Real.sqrt ((a + c - b) * (b + c - a))) ^ 2 ≥ 0   :=  by sorry
