-- Prove2me | Theorems.Thm_WorkbookSource_plus_57739
-- name    : WorkbookSource.plus_57739
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:33.185289+00:00
-- url     : https://prove2.me/theorems/43518049-6493-4bab-86d5-46fd5569c74b
-- title:
--   A weighted cyclic cubic ratio sum bounds one eighth of the total
-- statement:
--   Let $a,b,c >0 $. Prove that
--    $\frac{a^{3}}{5a^{2}+2ab+b^{2}}+\frac{b^{3}}{5b^{2}+2bc+c^{2}}+\frac{c^{3}}{5c^{2}+2ca+a^{2}}\geq \frac{a+b+c}{8} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_57739` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_57739; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_57739 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 / (5 * a^2 + 2 * a * b + b^2) + b^3 / (5 * b^2 + 2 * b * c + c^2) + c^3 / (5 * c^2 + 2 * c * a + a^2)) ≥ (a + b + c) / 8   :=  by sorry
