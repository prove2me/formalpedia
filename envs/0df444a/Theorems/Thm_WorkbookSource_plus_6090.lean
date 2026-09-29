-- Prove2me | Theorems.Thm_WorkbookSource_plus_6090
-- name    : WorkbookSource.plus_6090
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:07.811796+00:00
-- url     : https://prove2.me/theorems/433ffe12-4874-4df7-b3db-66136d22e579
-- title:
--   A shifted mixed product ratio upper bound
-- statement:
--   If $ a,b,c > 0$ , then
--
--    $ \frac {ab + 3c}{a + b + 2c} + \frac {ca + 3b}{a + 2b + c} + \frac {bc + 3a}{2a + b + c}\leq\frac {a + b + c + 9}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_6090` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_6090; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_6090 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b + 3 * c) / (a + b + 2 * c) + (c * a + 3 * b) / (a + 2 * b + c) + (b * c + 3 * a) / (2 * a + b + c) ≤ (a + b + c + 9) / 4   :=  by sorry
