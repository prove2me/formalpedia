-- Prove2me | Theorems.Thm_lean_workbook_plus_14679
-- name    : lean_workbook_plus_14679
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/17db30b5-bebe-4278-a21f-606679b87c0a
-- statement:
--   Prove that $\frac{(2n)!}{n!(n+1)!}$ is a whole number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14679 (n : ℕ) : ∃ k : ℕ, (2 * n)! / (n! * (n + 1)!) = k   :=  by sorry
