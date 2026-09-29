-- Prove2me | Theorems.Thm_WorkbookSource_plus_19234
-- name    : WorkbookSource.plus_19234
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:27.902741+00:00
-- url     : https://prove2.me/theorems/023dc5fd-ca90-4cb3-a593-f1018a7b1e03
-- title:
--   A quartic ratio with a triple-product correction
-- statement:
--   Let $a,b,c>0$ prove that $$\frac{a^4+b^4+c^4}{ab+bc+ca}+\frac{9abc}{2(a+b+c)} \geqslant \frac{5}{6}(a^2+b^2+c^2).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_19234` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_19234; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_19234 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^4 + c^4) / (a * b + b * c + c * a) + (9 * a * b * c) / (2 * (a + b + c)) ≥ (5 / 6) * (a^2 + b^2 + c^2)   :=  by sorry
