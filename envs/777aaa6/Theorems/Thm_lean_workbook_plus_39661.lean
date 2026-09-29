-- Prove2me | Theorems.Thm_lean_workbook_plus_39661
-- name    : lean_workbook_plus_39661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a835b411-d552-4720-8b5c-67e8c743be6a
-- statement:
--   $ a\equiv b$ (mod m) if and only if $ m|(a-b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39661 (a b m : ℤ) : a ≡ b [ZMOD m] ↔ m ∣ (a - b)   :=  by sorry
