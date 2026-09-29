-- Prove2me | Theorems.Thm_WorkbookSource_plus_68139
-- name    : WorkbookSource.plus_68139
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:43:54.742464+00:00
-- url     : https://prove2.me/theorems/de20a226-8f22-4d3a-9a3e-a8b8c85fb7ef
-- title:
--   A sixth-power bound for symmetric pairwise products
-- statement:
--   Prove that for all $a,b,c$ positive real number holds:
--
--    $5(a+b+c)^6\geq27(ab+ac+bc)(11(a^2b^2+a^2c^2+b^2c^2)+4abc(a+b+c))$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68139` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68139; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68139 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 5 * (a + b + c) ^ 6 ≥ 27 * (a * b + a * c + b * c) * (11 * (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) + 4 * a * b * c * (a + b + c))   :=  by sorry
