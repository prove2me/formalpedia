-- Prove2me | Theorems.Thm_lean_workbook_plus_39784
-- name    : lean_workbook_plus_39784
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b2559843-706a-4215-87a2-a734432f9f86
-- statement:
--   If $a,b,c$ are reals such that $a,b,c \ge 1$ and $a^2+b^2+c^2=6$ , show that $a+b+c \ge 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39784 (a b c : ℝ) (h1 : a ≥ 1 ∧ b ≥ 1 ∧ c ≥ 1 ∧ a^2 + b^2 + c^2 = 6) : a + b + c ≥ 4   :=  by sorry
