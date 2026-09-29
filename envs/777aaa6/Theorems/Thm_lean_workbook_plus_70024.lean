-- Prove2me | Theorems.Thm_lean_workbook_plus_70024
-- name    : lean_workbook_plus_70024
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a7dc2c48-5bdf-485f-b922-839b7aee3df0
-- statement:
--   If a,b are natural numbers with $a\\ge b$ , then show that: \n $(b+1)(b+2)(a-b+1)(a-b+2)\\ge2(a+1)(a+2).$\nIt holds for all $a \\ge b \\ge 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70024 (a b : ℕ) (h₁ : 1 ≤ b) (h₂ : b ≤ a) :  (b + 1) * (b + 2) * (a - b + 1) * (a - b + 2) ≥ 2 * (a + 1) * (a + 2)   :=  by sorry
