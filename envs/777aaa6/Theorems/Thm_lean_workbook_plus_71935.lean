-- Prove2me | Theorems.Thm_lean_workbook_plus_71935
-- name    : lean_workbook_plus_71935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d07dd5dc-5e99-4a97-ae72-efce53461647
-- statement:
--   Prove that if $a | b$ , then $2^a-1 | 2^b-1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71935 {a b : ℕ} (h₁ : a ∣ b) : (2 ^ a - 1) ∣ (2 ^ b - 1)   :=  by sorry
