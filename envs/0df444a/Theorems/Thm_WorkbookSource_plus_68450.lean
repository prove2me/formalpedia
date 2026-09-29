-- Prove2me | Theorems.Thm_WorkbookSource_plus_68450
-- name    : WorkbookSource.plus_68450
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:18.121834+00:00
-- url     : https://prove2.me/theorems/0878bc7d-b1b0-4748-86a5-ec285d2b12b6
-- title:
--   A quadratic lower bound for three positive variables
-- statement:
--   Let $a,b,c > 0$ , prove that $3a^2 + 2b^2 + c^2 + 4ab + 2c(a + b) -2(6a + 5b + 3c) + 14 \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68450` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68450; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68450 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * a ^ 2 + 2 * b ^ 2 + c ^ 2 + 4 * a * b + 2 * c * (a + b) - 2 * (6 * a + 5 * b + 3 * c) + 14 ≥ 0   :=  by sorry
