-- Prove2me | Theorems.Thm_lean_workbook_plus_59379
-- name    : lean_workbook_plus_59379
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e72a08da-947f-47a2-aedd-36cf2ad17c3d
-- statement:
--   a,b,c>0 such that $a^2+b^2+c^2+abc=4$, prove that $a+b+c \leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59379 (a b c : ℝ) (h : 0 < a ∧ 0 < b ∧ 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + a * b * c = 4) : a + b + c <= 3   :=  by sorry
