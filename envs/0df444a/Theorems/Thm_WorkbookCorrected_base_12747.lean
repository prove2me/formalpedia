-- Prove2me | Theorems.Thm_WorkbookCorrected_base_12747
-- name    : WorkbookCorrected.base_12747
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:23.016988+00:00
-- url     : https://prove2.me/theorems/09dc6cb5-3565-41da-984f-71aa93935c80
-- title:
--   A cyclic cubic maximum at fixed sum
-- statement:
--   Prove that the maximum value of $x^2 y + y^2 z + z^2 x$ given $x+y+z = 9$ and $x,y,z$ are non-negative real numbers is 108
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12747` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12747; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_12747 : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 9), x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ 108) ∧ (∃ x y z : ℝ, (0 ≤ x) ∧ (0 ≤ y) ∧ (0 ≤ z) ∧ (x + y + z = 9) ∧ ( x ^ 2 * y + y ^ 2 * z + z ^ 2 * x  =  108  )) := by sorry
