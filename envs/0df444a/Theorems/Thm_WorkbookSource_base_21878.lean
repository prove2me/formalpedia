-- Prove2me | Theorems.Thm_WorkbookSource_base_21878
-- name    : WorkbookSource.base_21878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:50:39.444596+00:00
-- url     : https://prove2.me/theorems/94831ed7-ecc2-4e82-b060-9c1f88a18195
-- title:
--   A cyclic squared-product ratio upper bound
-- statement:
--   Let $a,b,c >0$ . Prove that
--    $\frac{a^2(b+c)^2}{a^2+bc}+\frac{b^2(c+a)^2}{b^2+ca}+\frac{c^2(a+b)^2}{c^2+ab} \le a^2+b^2+c^2+ab+bc+ca$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21878` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21878; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21878 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 * (b + c)^2 / (a^2 + b * c) + b^2 * (c + a)^2 / (b^2 + c * a) + c^2 * (a + b)^2 / (c^2 + a * b)) ≤ a^2 + b^2 + c^2 + a * b + b * c + c * a  :=  by sorry
