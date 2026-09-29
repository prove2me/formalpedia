-- Prove2me | Theorems.Thm_lean_workbook_plus_6643
-- name    : lean_workbook_plus_6643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/cba5262b-1cc7-41c1-96dc-f57719cdab75
-- statement:
--   If $x \equiv 0 \mod{ab}$ where $a$ and $b$ are coprime, then can we say, $x \equiv 0 \mod{a}$ and $x \equiv 0 \mod {b}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6643 (a b x : ℕ) (hab : Nat.Coprime a b) (h : x ≡ 0 [ZMOD a * b]) : x ≡ 0 [ZMOD a] ∧ x ≡ 0 [ZMOD b]   :=  by sorry
