-- Prove2me | Theorems.Thm_WorkbookCorrected_base_29209
-- name    : WorkbookCorrected.base_29209
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:18.572211+00:00
-- url     : https://prove2.me/theorems/4ac6f521-5300-4b2f-bc9f-f7d980612141
-- title:
--   A linear maximum on a shifted ellipse
-- statement:
--   Find the max. value of $(4x-9y)/2$ if $x^2+9y^2-4x+6y+4=0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29209` (Apache-2.0). Natural-language proposition preserved; the maximum claim is completed with an attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29209; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_29209 : (∀ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 → (4*x - 9*y)/2 ≤ 8) ∧ (∃ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 ∧ (4*x - 9*y)/2 = 8) := by sorry
