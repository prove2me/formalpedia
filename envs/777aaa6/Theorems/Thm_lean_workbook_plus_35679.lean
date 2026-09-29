-- Prove2me | Theorems.Thm_lean_workbook_plus_35679
-- name    : lean_workbook_plus_35679
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/12a56e64-38d4-4c4e-b21e-93ea961ba4d5
-- statement:
--   If $a\equiv b \ (mod \ m) $ and $ p\equiv q \ (mod \ m) $, prove that $ab\equiv pq \ (mod \ m) $ and $a+b\equiv p+q \ (mod \ m) $.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35679 (a b m : ℕ) (p q : ℕ) (h1 : a ≡ b [ZMOD m]) (h2 : p ≡ q [ZMOD m]) : a * p ≡ b * q [ZMOD m] ∧ a + p ≡ b + q [ZMOD m]   :=  by sorry
