-- Prove2me | Theorems.Thm_lean_workbook_plus_14173
-- name    : lean_workbook_plus_14173
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/68b5ac15-7451-41ac-a02b-2113d02f9d30
-- statement:
--   Given the inequality $\sqrt{abc} \leq 1$, deduce that $abc \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14173 (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) (habc : a * b * c = 1) (h : Real.sqrt (a * b * c) ≤ 1) : a * b * c ≤ 1   :=  by sorry
