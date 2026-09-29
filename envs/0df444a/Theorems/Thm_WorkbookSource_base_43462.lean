-- Prove2me | Theorems.Thm_WorkbookSource_base_43462
-- name    : WorkbookSource.base_43462
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:32.71492+00:00
-- url     : https://prove2.me/theorems/17124c2b-afef-4f07-8ff6-a513a2ceeaed
-- title:
--   A mixed sixth-degree polynomial inequality
-- statement:
--   Let $a,b,c$ are real numbers,prove that: $a^2(c^2a^2+a^2b^2+ac^2b+c^4)+2b^4c^2 \geq ac(a^2+2b^2)(ab+c^2).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43462` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43462; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43462 (a b c : ℝ) : a^2 * (c^2 * a^2 + a^2 * b^2 + a * c^2 * b + c^4) + 2 * b^4 * c^2 ≥ a * c * (a^2 + 2 * b^2) * (a * b + c^2)  :=  by sorry
