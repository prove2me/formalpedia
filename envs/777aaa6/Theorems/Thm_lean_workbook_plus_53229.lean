-- Prove2me | Theorems.Thm_lean_workbook_plus_53229
-- name    : lean_workbook_plus_53229
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c6d9577d-68ab-4b93-bcf1-27109c00a1c1
-- statement:
--   if $a \equiv 2 \mod 3$ then $a^{3}-a\equiv2-2=0 \mod 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53229 : a ≡ 2 [ZMOD 3] → a^3 - a ≡ 0 [ZMOD 3]   :=  by sorry
