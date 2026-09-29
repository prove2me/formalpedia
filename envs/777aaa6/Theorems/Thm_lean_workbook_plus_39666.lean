-- Prove2me | Theorems.Thm_lean_workbook_plus_39666
-- name    : lean_workbook_plus_39666
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e84ce204-cec2-47e7-afce-7aa4edd04ca9
-- statement:
--   Prove $ n^7 - n \equiv 0 \pmod 2$ for any integer $ n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39666 : ∀ n : ℤ, n ^ 7 - n ≡ 0 [ZMOD 2]   :=  by sorry
