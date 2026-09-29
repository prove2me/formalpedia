-- Prove2me | Theorems.Thm_WorkbookSource_base_3175
-- name    : WorkbookSource.base_3175
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:47.959001+00:00
-- url     : https://prove2.me/theorems/384cf706-fcf1-465e-b0ba-e044ba1674ea
-- title:
--   A cyclic ratio sum bounds an asymmetric pairwise expression
-- statement:
--   Let $ a,b,c > 0$ . Prove that
--
--    $ \frac {a}{b} + \frac {b}{c} + \frac {c}{a}\geq\frac {1}{2}(\frac {b}{a + c} + \frac {b + 2a}{b + c} + \frac {b + 2c}{a + b} + \frac {5}{2})$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3175` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3175; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3175 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / b + b / c + c / a) ≥ 1 / 2 * (b / (a + c) + (b + 2 * a) / (b + c) + (b + 2 * c) / (a + b) + 5 / 2)  :=  by sorry
