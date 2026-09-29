-- Prove2me | Theorems.Thm_lean_workbook_plus_80804
-- name    : lean_workbook_plus_80804
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/50095c48-e48e-4c7a-8743-18c2bd32503b
-- statement:
--   Find the value of $\sum\limits_{k=1}^{100} k^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80804 : ∑ k in Finset.range 101, k^2 = 338350   :=  by sorry
