-- Prove2me | Theorems.Thm_lean_workbook_plus_80593
-- name    : lean_workbook_plus_80593
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b8de8c22-8270-4e95-8e5f-af258d9cea17
-- statement:
--   $ gcd(3 * \overbrace{11\cdots 1}^{30},2 * \overbrace{11\cdots 1}^{30}) = \overbrace{11\cdots 1}^{30}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80593 :
  Nat.gcd (3 * 11^30) (2 * 11^30) = 11^30   :=  by sorry
