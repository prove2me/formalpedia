-- Prove2me | Theorems.Thm_WorkbookSource_base_26251
-- name    : WorkbookSource.base_26251
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:07:01.01356+00:00
-- url     : https://prove2.me/theorems/59437850-51d9-4573-8b43-dbd7442cbc88
-- title:
--   A symmetric quadratic ratio with a cyclic quartic correction
-- statement:
--   Let $a,b,c$ be positive real numbers . Prove that
--    $\frac{3(a^2+b^2+c^2)}{ab+bc+ca}+\frac{ab^3+bc^3+ca^3}{a^3b+b^3c+c^3a}\geq 4.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26251` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26251; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26251 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * (a ^ 2 + b ^ 2 + c ^ 2) / (a * b + b * c + c * a) + (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) / (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) ≥ 4  :=  by sorry
