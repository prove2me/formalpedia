-- Prove2me | Theorems.Thm_lean_workbook_plus_14124
-- name    : lean_workbook_plus_14124
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7da35ea1-6052-4517-af0b-0ea7ede77927
-- statement:
--   Let $ a_1=\cos(1)$ , $ a_{n+1}=\max\{a_n,\cos(n+1)\},n\ge1$ .Does $ \lim_{n\rightarrow\infty}{a_n}$ exist? Explain.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14124 : ∃ a : ℕ → ℝ, a 1 = Real.cos 1 ∧ ∀ n, a (n + 1) = max (a n) (Real.cos (n + 1))   :=  by sorry
