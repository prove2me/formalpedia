-- Prove2me | Theorems.Thm_lean_workbook_plus_705
-- name    : lean_workbook_plus_705
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d629192a-87e6-4884-bf39-7384e8e55222
-- statement:
--   Prove that $A_n=A_1+n-1=1+n-1=n,\forall n\in\mathbb{N^*}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_705 (n : ℕ) (hn : 0 < n) : n = 1 + n - 1   :=  by sorry
