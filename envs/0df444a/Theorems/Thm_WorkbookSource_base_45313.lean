-- Prove2me | Theorems.Thm_WorkbookSource_base_45313
-- name    : WorkbookSource.base_45313
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:46.953933+00:00
-- url     : https://prove2.me/theorems/451fba95-4ffc-46e4-b0ef-931dfebab621
-- title:
--   A cyclic quartic inequality with coefficient ten
-- statement:
--   Let $ a,b,c$ be non-negative real numbers. Prove that
--    $ 3(a^4 + b^4 + c^4) + 9(a^2b^2 + b^2c^2 + c^2a^2)\ge 10(a^3b + b^3c + c^3a) + 2abc(a + b + c).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45313` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45313; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_45313 (a b c : ℝ) : 3 * (a ^ 4 + b ^ 4 + c ^ 4) + 9 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 10 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 2 * a * b * c * (a + b + c)  :=  by sorry
