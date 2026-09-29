-- Prove2me | Theorems.Thm_lean_workbook_plus_23949
-- name    : lean_workbook_plus_23949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/6713d19b-ec9f-455e-87a6-f0e27b33758c
-- statement:
--   Prove that if $a \equiv b \pmod m$ and $n | m$ , then $a \equiv b \pmod n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23949 (a b m n : ℤ) (h₁ : a ≡ b [ZMOD m]) (h₂ : n ∣ m) : a ≡ b [ZMOD n]   :=  by sorry
