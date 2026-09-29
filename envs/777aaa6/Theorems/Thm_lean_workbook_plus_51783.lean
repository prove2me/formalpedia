-- Prove2me | Theorems.Thm_lean_workbook_plus_51783
-- name    : lean_workbook_plus_51783
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ade6370b-2e83-46cc-8079-6ab609b7a0c3
-- statement:
--   Prove that $\sum_{n=1}^{2021} \frac{1}{3^n} < \frac{1}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51783 : ∑ n in Finset.Icc 1 2021, (1 / (3 ^ n)) < 1 / 2   :=  by sorry
