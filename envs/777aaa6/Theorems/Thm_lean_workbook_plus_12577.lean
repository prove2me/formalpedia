-- Prove2me | Theorems.Thm_lean_workbook_plus_12577
-- name    : lean_workbook_plus_12577
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/746a6525-ebe6-45ff-95b1-c422b5ca06e9
-- statement:
--   So, $ N=2(100+99+98+\dots +1)=2(5050)=10100$ . Answer is then $ \boxed{100}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12577 :
  (∑ k in (Finset.range 101), 2 * (101 - k)) = 10100   :=  by sorry
