-- Prove2me | Theorems.Thm_lean_workbook_plus_62545
-- name    : lean_workbook_plus_62545
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4990d7ad-bd76-4506-be2a-507f9165628b
-- statement:
--   If $a\equiv b \bmod{m}$ , then is $na\equiv nb \bmod{nm}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62545 (n m a b : ℤ) (h₁ : n > 0 ∧ m > 0) (hab : a ≡ b [ZMOD m]) : n * a ≡ n * b [ZMOD n * m]   :=  by sorry
