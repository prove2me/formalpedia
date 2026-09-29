-- Prove2me | Theorems.Thm_lean_workbook_plus_46990
-- name    : lean_workbook_plus_46990
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/b9910d01-c0b5-44a0-bdf0-02f8ddc244e9
-- statement:
--   Let S = $\displaystyle\sum_{r=1}^n \ r$ and T = $\displaystyle\sum_{r=1}^n \ (n+1-r)$ . Show that T = S.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46990 : ∀ n : ℕ, (∑ r in Finset.range n, (n + 1 - r)) = (∑ r in Finset.range n, r)   :=  by sorry
