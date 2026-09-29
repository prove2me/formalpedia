-- Prove2me | Theorems.Thm_lean_workbook_plus_27538
-- name    : lean_workbook_plus_27538
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6d28c217-cfdc-4bda-a526-be01226b0f61
-- statement:
--   Solve the equation $ 108x \equiv 171 (mod 529)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27538 (x : ℕ) : 108 * x ≡ 171 [ZMOD 529] ↔ x ≡ 222 [ZMOD 529]   :=  by sorry
