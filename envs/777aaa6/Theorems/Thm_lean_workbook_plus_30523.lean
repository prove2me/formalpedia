-- Prove2me | Theorems.Thm_lean_workbook_plus_30523
-- name    : lean_workbook_plus_30523
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/85a80ca9-d233-4056-baac-50ce149174bd
-- statement:
--   By Wilson's theorem $12! \equiv -1 (mod 13)$ and $10! \equiv 12! \times 12^{-1} \times 11^{-1} \equiv (-1) \times (-1) \times 6 =6(mod 13)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30523 :
  (12! ≡ -1 [ZMOD 13]) ∧ (10! ≡ 6 [ZMOD 13])   :=  by sorry
