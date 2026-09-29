-- Prove2me | Theorems.Thm_lean_workbook_plus_34018
-- name    : lean_workbook_plus_34018
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f56871c8-d2d0-4a58-a329-015d9e2042e7
-- statement:
--   Given $a \equiv b \pmod{n}$, prove that $a + c \equiv b + c \pmod{n}$ for any integer $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34018 {a b c n : ℤ} (h₁ : a ≡ b [ZMOD n]) : a + c ≡ b + c [ZMOD n]   :=  by sorry
