-- Prove2me | Theorems.Thm_lean_workbook_plus_4730
-- name    : lean_workbook_plus_4730
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e17106d9-2278-4962-83a7-5de217ae525c
-- statement:
--   Factorization: $S=\frac{2005\times 2004\times 2003}{3!}=\frac{(5\times 401)\times(2^2\times 3\times 167)\times 2003}{2\times 3}=2\times 5\times 167\times 401\times 2003$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4730 :
  2005 * 2004 * 2003 / 3! = 2 * 5 * 167 * 401 * 2003   :=  by sorry
