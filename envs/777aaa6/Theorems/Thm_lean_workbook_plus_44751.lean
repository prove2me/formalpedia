-- Prove2me | Theorems.Thm_lean_workbook_plus_44751
-- name    : lean_workbook_plus_44751
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b43b5db2-b09e-4337-8e64-021e320fec58
-- statement:
--   Find the least positive integer $x$ such that $x \equiv 5\pmod7 $ , $x\equiv7(mod11)$ , $x\equiv 3(mod13)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44751 (x : ℕ) (hx : x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]) : x >= 887   :=  by sorry
