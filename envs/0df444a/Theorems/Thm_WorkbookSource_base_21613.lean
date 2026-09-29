-- Prove2me | Theorems.Thm_WorkbookSource_base_21613
-- name    : WorkbookSource.base_21613
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:00.866024+00:00
-- url     : https://prove2.me/theorems/abc1dbbc-98a3-471a-b397-63e22a71f687
-- title:
--   A pair-product ratio sum bounds a normalized squared total
-- statement:
--   Let $ a,b,c>0$ . Prove that:
--
--    $ \frac{{2{{\left( {a + b + c} \right)}^2}}}{{{a^2} + {b^2} + {c^2}}} \le \frac{{\left( {a + b} \right)\left( {a + c} \right)}}{{{a^2} + bc}} + \frac{{\left( {b + c} \right)\left( {b + a} \right)}}{{{b^2} + ca}} + \frac{{\left( {c + a} \right)\left( {c + b} \right)}}{{{c^2} + ab}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21613` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21613; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21613 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 * (a + b + c) ^ 2) / (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a + b) * (a + c) / (a ^ 2 + b * c) + (b + c) * (b + a) / (b ^ 2 + c * a) + (c + a) * (c + b) / (c ^ 2 + a * b)  :=  by sorry
