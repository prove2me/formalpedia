-- Prove2me | Theorems.Thm_lean_workbook_plus_2141
-- name    : lean_workbook_plus_2141
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/46d4e6cd-d14f-40bd-a970-4be1a7a2d531
-- statement:
--   And $a_m|a_{m+1}$ $\implies$ $\gcd(a_m,a_{m+1})=a_m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2141 (a : ℕ → ℕ) (h : ∀ m, a m ∣ a (m + 1)) : ∀ m, m < n → Nat.gcd (a m) (a (m + 1)) = a m   :=  by sorry
