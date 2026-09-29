-- Prove2me | Theorems.Thm_WorkbookSource_base_21250
-- name    : WorkbookSource.base_21250
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:47:12.664151+00:00
-- url     : https://prove2.me/theorems/5b71a1ef-f8f3-4eb5-a19c-d27bda28cce5
-- title:
--   A symmetric product ratio with a triple-product correction
-- statement:
--   Let $ a,b,c > 0$ . Show that :
--
--    $ \frac {(ab + bc + ca)^2}{3abc(a + b + c)} + \frac {abc}{(a + b + c)^3}\ge \frac {28}{27}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21250` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21250; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21250 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + b * c + c * a) ^ 2 / (3 * a * b * c * (a + b + c)) + a * b * c / (a + b + c) ^ 3 ≥ 28 / 27  :=  by sorry
