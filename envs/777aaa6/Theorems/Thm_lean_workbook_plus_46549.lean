-- Prove2me | Theorems.Thm_lean_workbook_plus_46549
-- name    : lean_workbook_plus_46549
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/15856c0b-6df2-465a-a306-826efdcafd59
-- statement:
--   Show that $2^{k+1}(k+1)!<2(k+1)^{k+1}<(1+\frac{1}{k+1})^{k+1} (k+1)^{k+1} = (k+2)^{k+1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46549 : ∀ k : ℕ, 2 ^ (k + 1) * (k + 1)! < 2 * (k + 1) ^ (k + 1) ∧ 2 * (k + 1) ^ (k + 1) < (1 + 1 / (k + 1)) ^ (k + 1) * (k + 1) ^ (k + 1)   :=  by sorry
