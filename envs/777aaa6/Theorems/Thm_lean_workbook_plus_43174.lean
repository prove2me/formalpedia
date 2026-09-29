-- Prove2me | Theorems.Thm_lean_workbook_plus_43174
-- name    : lean_workbook_plus_43174
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/132a2924-0e77-4b6e-961a-d0f9d5a3d6dd
-- statement:
--   Proving $e^{\cos x}\cos(\sin x)=\sum^{\infty}_{n=0}\frac{\cos(nx)}{n!}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43174 : ∀ x : ℝ, (Real.exp (Real.cos x)) * (Real.cos (Real.sin x)) = ∑' n : ℕ, (Real.cos (n * x)) / (n!)   :=  by sorry
