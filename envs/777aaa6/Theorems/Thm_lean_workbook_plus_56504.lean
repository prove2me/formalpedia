-- Prove2me | Theorems.Thm_lean_workbook_plus_56504
-- name    : lean_workbook_plus_56504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/cd0c9f7d-1bf6-4d7b-b33a-95481bbe486d
-- statement:
--   Since $2^{10}\equiv 1\pmod{11}$ from Fermat's Little Theorem, the remainder is $2^8=256\equiv 3\pmod {11}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56504 :
  (2^8) % 11 = 3   :=  by sorry
