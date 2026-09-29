-- Prove2me | Theorems.Thm_WorkbookSource_plus_20327
-- name    : WorkbookSource.plus_20327
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:24.808391+00:00
-- url     : https://prove2.me/theorems/f37e19af-1f16-4b63-b98d-412ca0d48806
-- title:
--   An even polynomial has no real roots
-- statement:
--   Prove that the equation $8x^8 + 3x^6 + 5x^4 + 3x^2 + 10 = 0$ has no real roots.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20327` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20327; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20327 : ¬ (∃ x : ℝ, 8*x^8 + 3*x^6 + 5*x^4 + 3*x^2 + 10 = 0)   :=  by sorry
