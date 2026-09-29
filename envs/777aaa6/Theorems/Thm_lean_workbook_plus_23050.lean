-- Prove2me | Theorems.Thm_lean_workbook_plus_23050
-- name    : lean_workbook_plus_23050
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/bd9cbe5a-a95f-471b-9cb1-af3bdab9b6cc
-- statement:
--   Prove that $1+2+3+4+\cdots+n = \frac{n(n+1)}{2}$ using induction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23050 : ∀ n, ∑ i in Finset.range (n+1), i = n * (n + 1) / 2   :=  by sorry
