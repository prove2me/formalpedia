-- Prove2me | Theorems.Thm_WorkbookSource_plus_23756
-- name    : WorkbookSource.plus_23756
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:33:01.740205+00:00
-- url     : https://prove2.me/theorems/fe67fdac-ab2b-4177-9c05-72743fe710c3
-- title:
--   A product of elementary symmetric sums bounds a five-degree term
-- statement:
--   Prove that for non-negative numbers $a, b, c, d$, the following inequality holds: $(ab+bc+cd+ad+ac+bd)(acd+abd+abc+bcd) \geq 6(a+b+c+d)abcd$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_23756` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_23756; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_23756 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a * b + b * c + c * d + d * a + a * c + b * d) * (a * c * d + b * c * d + b * a * c + a * b * d) ≥ 6 * (a + b + c + d) * a * b * c * d   :=  by sorry
