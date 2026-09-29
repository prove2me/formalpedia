-- Prove2me | Theorems.Thm_lean_workbook_plus_37106
-- name    : lean_workbook_plus_37106
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/42c00df7-92e1-4ea2-bd85-17cb9d4dd630
-- statement:
--   in the expression $x = 2^a \cdot 3^b \cdot 5^c \cdot 7^d$ we have $x=1$ only when $a=b=c=d=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37106 (x a b c d : ℕ) (hx : x = 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) : x = 1 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0   :=  by sorry
