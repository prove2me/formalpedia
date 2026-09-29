-- Prove2me | Theorems.Thm_WorkbookSource_plus_19763
-- name    : WorkbookSource.plus_19763
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:15.487631+00:00
-- url     : https://prove2.me/theorems/fcab7ad6-e01c-4e33-a9de-d8e763f1c55b
-- title:
--   A cubic sum bound on the unit simplex
-- statement:
--   Let $ a,b,c\ge 0$ such that $ a + b + c = 1$ . Prove that $ a^3 + b^3 + c^3\le 3(1 + abc)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_19763` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_19763; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_19763 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1) :
  a^3 + b^3 + c^3 ≤ 3 * (1 + a * b * c)   :=  by sorry
