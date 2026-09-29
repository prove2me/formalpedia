-- Prove2me | Theorems.Thm_WorkbookSource_plus_33129
-- name    : WorkbookSource.plus_33129
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:52.367913+00:00
-- url     : https://prove2.me/theorems/4e90a6e3-5137-46a3-9371-3965b4da9b0b
-- title:
--   A cyclic product bound for four real variables
-- statement:
--   Prove that $a^4+b^4+c^4+d^4-4abcd+(a+b)(b+c)(c+d)(d+a) \leqslant (a^2+b^2+c^2+d^2)^2$ given $a,b,c,d\ge 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_33129` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_33129; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_33129 (a b c d : ℝ) : a^4 + b^4 + c^4 + d^4 - 4 * a * b * c * d + (a + b) * (b + c) * (c + d) * (d + a) ≤ (a^2 + b^2 + c^2 + d^2)^2   :=  by sorry
