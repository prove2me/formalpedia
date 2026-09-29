-- Prove2me | Theorems.Thm_lean_workbook_plus_34337
-- name    : lean_workbook_plus_34337
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/5ab09bee-aa75-4193-aaa6-0a2f484fe9fe
-- statement:
--   Prove that for every $x\geq1$ : $1-\frac{1}{x} \leq \ln x<1+x$ using definite integrals
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34337 (x : ℝ) (hx : 1 ≤ x) : 1 - 1 / x ≤ Real.log x ∧ Real.log x < 1 + x   :=  by sorry
