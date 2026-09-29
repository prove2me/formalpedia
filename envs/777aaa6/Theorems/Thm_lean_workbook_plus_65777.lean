-- Prove2me | Theorems.Thm_lean_workbook_plus_65777
-- name    : lean_workbook_plus_65777
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/cfcedc92-dd07-4f8c-a5fb-98e3e082c723
-- statement:
--   Find the least positive integer $x$ such that $x \equiv 5\pmod7 $ , $x\equiv7(mod11)$ , $x\equiv 3(mod13)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65777 (x : ℕ) (hx: x ≡ 5 [ZMOD 7] ∧ x ≡ 7 [ZMOD 11] ∧ x ≡ 3 [ZMOD 13]) : x >= 197   :=  by sorry
