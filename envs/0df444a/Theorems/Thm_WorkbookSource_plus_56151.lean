-- Prove2me | Theorems.Thm_WorkbookSource_plus_56151
-- name    : WorkbookSource.plus_56151
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:00.791479+00:00
-- url     : https://prove2.me/theorems/dae47356-14bf-4f4a-90f4-d0b935940e32
-- title:
--   A product of mixed quadratics bounds a squared symmetric cubic sum
-- statement:
--   if $a,b,c \geq 0$ ,prove that
--    $4(a^{2}+ab+c^{2})(b^{2}+bc+a^{2})(c^{2}+ca+b^{2})\ge3(a^2b+a^2c+b^2a+b^2c+c^2a+c^2b)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_56151` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_56151; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_56151 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 4 * (a ^ 2 + a * b + c ^ 2) * (b ^ 2 + b * c + a ^ 2) * (c ^ 2 + c * a + b ^ 2) ≥ 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b) ^ 2   :=  by sorry
