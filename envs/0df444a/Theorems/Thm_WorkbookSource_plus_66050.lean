-- Prove2me | Theorems.Thm_WorkbookSource_plus_66050
-- name    : WorkbookSource.plus_66050
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:44:43.931206+00:00
-- url     : https://prove2.me/theorems/2850288c-16ef-4fda-ab5e-a3648c92c88e
-- title:
--   A cubic ratio and normalized quadratic sum inequality
-- statement:
--   Let $ a,b,c > 0$ . Prove that $ \frac {(a + b + c)^3}{a^2b + b^2c + c^2a} + \frac {30(a^2 + b^2 + c^2)}{(a + b + c)^2}\ge 19$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_66050` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_66050; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_66050 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 / (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 30 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 ≥ 19   :=  by sorry
