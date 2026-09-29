-- Prove2me | Theorems.Thm_lean_workbook_plus_26977
-- name    : lean_workbook_plus_26977
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/86f27cf6-e36d-463f-81fd-8ac50ac88ce5
-- statement:
--   If $a\equiv 0\mod 3$ then $a-1\equiv 2\mod 3$ and $2a+1\equiv 1\mod 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26977 : ∀ a : ℤ, a % 3 = 0 → (a - 1) % 3 = 2 ∧ (2 * a + 1) % 3 = 1   :=  by sorry
