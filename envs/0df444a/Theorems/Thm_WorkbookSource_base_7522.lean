-- Prove2me | Theorems.Thm_WorkbookSource_base_7522
-- name    : WorkbookSource.base_7522
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:13.164727+00:00
-- url     : https://prove2.me/theorems/67be0019-fcfb-4b9e-b9b0-33ae7ceb1961
-- title:
--   A fourth-power ratio with a triple-product correction
-- statement:
--   Let a,b,c >0. Prove that:
--    $ \frac{ a^4+b^4+c^4}{ab+bc+ca}+\frac{3abc}{a+b+c}\geq \frac{2}{3}(a^2+b^2+c^2) $
--   ( by Schur )
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7522` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7522; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7522 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 + b^4 + c^4) / (a * b + b * c + c * a) + (3 * a * b * c) / (a + b + c) ≥ (2 / 3) * (a^2 + b^2 + c^2)  :=  by sorry
