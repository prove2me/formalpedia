-- Prove2me | Theorems.Thm_lean_workbook_plus_45385
-- name    : lean_workbook_plus_45385
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3ad8a283-e78b-4a66-8159-03f7657828aa
-- statement:
--   Show that $\sum_{n=0}^k \binom{k+n}{2n}=\sum_{n=0}^k \binom{k+n}{k-n}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45385 (k : ℕ) : ∑ n in Finset.range (k+1), choose (k + n) (2 * n) = ∑ n in Finset.range (k+1), choose (k + n) (k - n)   :=  by sorry
