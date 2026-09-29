-- Prove2me | Theorems.Thm_lean_workbook_plus_57479
-- name    : lean_workbook_plus_57479
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/482f8417-5f22-4277-9a08-24a5c74908e3
-- statement:
--   Prove that if a polynomial $P(x)$ satisfies $P(x) = P(x-1)$ for all real numbers $x$, then $P$ is constant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57479 (P : Polynomial ℝ) (h : ∀ x, P.eval x = P.eval (x - 1)) : ∃ c, P = c   :=  by sorry
