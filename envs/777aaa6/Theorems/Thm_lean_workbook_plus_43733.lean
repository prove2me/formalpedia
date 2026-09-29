-- Prove2me | Theorems.Thm_lean_workbook_plus_43733
-- name    : lean_workbook_plus_43733
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/5071f6f8-63e4-4106-8b42-2cd7188225af
-- statement:
--   Find solutions to $x^2\equiv 1\pmod{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43733 (x : ℕ) : x^2 ≡ 1 [ZMOD 5] ↔ x ≡ 1 [ZMOD 5] ∨ x ≡ 4 [ZMOD 5]   :=  by sorry
