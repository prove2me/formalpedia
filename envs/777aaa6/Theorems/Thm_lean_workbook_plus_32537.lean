-- Prove2me | Theorems.Thm_lean_workbook_plus_32537
-- name    : lean_workbook_plus_32537
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/356259b3-02bb-4b55-a829-0880efecdb52
-- statement:
--   Prove that the sum is equal to $\frac{1}{2}-\frac{1}{101}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32537 :
  ∑ k in (Finset.Icc 1 100), (1 / (k^2 + k + 1) - 1 / (k^2 + k + 2)) = 1 / 2 - 1 / 101   :=  by sorry
