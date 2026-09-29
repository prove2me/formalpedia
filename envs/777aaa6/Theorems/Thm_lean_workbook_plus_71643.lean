-- Prove2me | Theorems.Thm_lean_workbook_plus_71643
-- name    : lean_workbook_plus_71643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/70b540bb-b0aa-4c54-b0f2-98854bbcfebc
-- statement:
--   Prove that $3$ divides both $(a-2)(a-1)a$ and $a(a+1)(a+2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71643 (a : ℕ) : 3 ∣ (a-2)*(a-1)*a ∧ 3 ∣ a*(a+1)*(a+2)   :=  by sorry
