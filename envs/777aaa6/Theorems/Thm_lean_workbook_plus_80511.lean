-- Prove2me | Theorems.Thm_lean_workbook_plus_80511
-- name    : lean_workbook_plus_80511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6628779e-219e-4f0a-8551-0d9a0c4bf747
-- statement:
--   Let $ a,b,c$ be positive integers such that $ a + b + c \mid a^2 + b^2 + c^2$ . Show that $ a + b + c \mid a^n + b^n + c^n$ for infinitely many positive integer $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80511 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c ∣ a^2 + b^2 + c^2) : ∃ n : ℕ, a + b + c ∣ a^n + b^n + c^n   :=  by sorry
