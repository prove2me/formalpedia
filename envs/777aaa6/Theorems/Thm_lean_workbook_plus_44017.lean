-- Prove2me | Theorems.Thm_lean_workbook_plus_44017
-- name    : lean_workbook_plus_44017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/ebd05fd2-42c9-4f65-9346-94910fd1d33f
-- statement:
--   Find the last three digits of the number $2003^{{2002}^{2001}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44017 : 2003 ^ ((2002 ^ 2001) % 10000) ≡ 241 [MOD 1000]   :=  by sorry
