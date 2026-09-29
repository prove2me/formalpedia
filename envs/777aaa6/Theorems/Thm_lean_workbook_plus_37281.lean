-- Prove2me | Theorems.Thm_lean_workbook_plus_37281
-- name    : lean_workbook_plus_37281
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/247fdb67-f1ce-4034-941f-8d95f979ab0d
-- statement:
--   Find the value of \(\sum_{k=1}^{20} k\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37281 : ∑ k in Finset.range 20, k = 210   :=  by sorry
