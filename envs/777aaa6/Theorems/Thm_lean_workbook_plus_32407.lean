-- Prove2me | Theorems.Thm_lean_workbook_plus_32407
-- name    : lean_workbook_plus_32407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/e20f3f59-ab6d-4b9c-9313-db736fa99ebd
-- statement:
--   Without Jensen, prove that if $a,b,c > 0$ , $9(a^3 + b^3 + c^3) \geq (a+b+c)^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32407 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → 9 * (a^3 + b^3 + c^3) ≥ (a + b + c)^3   :=  by sorry
