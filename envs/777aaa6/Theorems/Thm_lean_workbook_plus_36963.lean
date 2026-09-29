-- Prove2me | Theorems.Thm_lean_workbook_plus_36963
-- name    : lean_workbook_plus_36963
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/ceda3584-470f-47ae-a0a0-6ea57cee731a
-- statement:
--   If $a\equiv b \pmod{c}$ , show that $a^{x}\equiv b^{x}\pmod{c}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36963 (a b c x : ℕ) (hab : a ≡ b [ZMOD c]) : a ^ x ≡ b ^ x [ZMOD c]   :=  by sorry
