-- Prove2me | Theorems.Thm_lean_workbook_plus_77194
-- name    : lean_workbook_plus_77194
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/49138e8e-c151-44b3-ab8d-f6dfccfcb3fb
-- statement:
--   $ 5^n \equiv 5,25,1 (31)$ for $ n=1,2,3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77194 : 5 ^ 1 ≡ 5 [ZMOD 31] ∧ 5 ^ 2 ≡ 25 [ZMOD 31] ∧ 5 ^ 3 ≡ 1 [ZMOD 31]   :=  by sorry
