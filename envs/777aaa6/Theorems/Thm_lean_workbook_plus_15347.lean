-- Prove2me | Theorems.Thm_lean_workbook_plus_15347
-- name    : lean_workbook_plus_15347
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0ff7280c-d85e-4b88-87f7-63bf5f81a496
-- statement:
--   Prove by induction: 1= $1*1!+2*2!+..+n*n!=(n+1)!-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15347 : ∀ n, ∑ i in Finset.range n, i * i! = (n + 1)! - 1   :=  by sorry
