-- Prove2me | Theorems.Thm_lean_workbook_plus_6876
-- name    : lean_workbook_plus_6876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/91571055-7ad2-4416-8cd6-1be356fa42ae
-- statement:
--   Show that if $b$ divides $a$, then $2^b-1$ divides $2^a-1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6876 : ∀ {a b : ℕ}, b ∣ a → (2 ^ b - 1) ∣ (2 ^ a - 1)   :=  by sorry
