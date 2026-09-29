-- Prove2me | Theorems.Thm_lean_workbook_plus_15030
-- name    : lean_workbook_plus_15030
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/578223d4-4d31-4c62-86a6-3c51fef43fe8
-- statement:
--   Find the LCM. $243=3^5$ . $225=3^2\times5^2$ . The LCM is the smallest possible prime factorization that contains both.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15030 :
  Nat.lcm 243 225 = 3^5 * 5^2   :=  by sorry
