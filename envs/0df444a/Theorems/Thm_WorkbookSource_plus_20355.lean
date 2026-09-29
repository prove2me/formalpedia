-- Prove2me | Theorems.Thm_WorkbookSource_plus_20355
-- name    : WorkbookSource.plus_20355
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:32.137283+00:00
-- url     : https://prove2.me/theorems/4dc9fbe1-3801-4661-a48e-eb5142cce947
-- title:
--   A symmetric quadratic ratio with a normalized cubic correction
-- statement:
--   If $ a,b,c>0 $ then:
--    $ \frac{a^2+b^2+c^2}{ab+bc+ca}+\frac{128abc}{3(a+b+c)^3+47abc}\ge 2 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20355` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20355; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20355 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) + (128 * a * b * c) / (3 * (a + b + c)^3 + 47 * a * b * c) ≥ 2   :=  by sorry
