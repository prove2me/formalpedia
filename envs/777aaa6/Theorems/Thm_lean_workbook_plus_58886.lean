-- Prove2me | Theorems.Thm_lean_workbook_plus_58886
-- name    : lean_workbook_plus_58886
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/cf3c40f0-8120-4f1e-85aa-691a702fbd02
-- statement:
--   Explain why taking the square root on both sides of an inequality, assuming $a > b > 0$, is a valid step to show that $\sqrt{a} > \sqrt{b}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58886 (a b : ℝ) (h₁ : a > b) (h₂ : b > 0) : Real.sqrt a > Real.sqrt b   :=  by sorry
