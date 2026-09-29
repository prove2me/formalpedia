-- Prove2me | Theorems.Thm_lean_workbook_plus_72900
-- name    : lean_workbook_plus_72900
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/550d359e-8249-497d-a05e-bda4a09a42e2
-- statement:
--   Does this infinite product converge?\n\n$\prod_{n=1}^{\infty}n\sin\left(\frac1n\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72900 : ∃ p, ∏' n : ℕ, n * Real.sin (1 / n) = p   :=  by sorry
