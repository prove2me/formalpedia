-- Prove2me | Theorems.Thm_lean_workbook_plus_49548
-- name    : lean_workbook_plus_49548
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5b9fb896-4c2b-4f6d-9183-b7d8dcf0858f
-- statement:
--   Find x such that: $11x \equiv 1 (mod 3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49548 (x : ℕ) : (11 * x ≡ 1 [ZMOD 3]) ↔ (x ≡ 2 [ZMOD 3])   :=  by sorry
