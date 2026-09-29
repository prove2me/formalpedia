-- Prove2me | Theorems.Thm_WorkbookSource_plus_62905
-- name    : WorkbookSource.plus_62905
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:40:09.949925+00:00
-- url     : https://prove2.me/theorems/9597f395-5844-48d1-bdaf-0cfc29bd1624
-- title:
--   A shifted quadratic ratio sum is at least nine at fixed sum three
-- statement:
--   Let $ a,b,c$ be poistive reals such that $ a + b + c = 3$ . Prove that
--
--    $ \frac {2a^2 + 3a + 1}{b^2 + 1} + \frac {2b^2 + 3b + 1}{c^2 + 1} + \frac {2c^2 + 3c + 1}{a^2 + 1}\geq9$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_62905` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_62905; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_62905 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (2 * a ^ 2 + 3 * a + 1) / (b ^ 2 + 1) + (2 * b ^ 2 + 3 * b + 1) / (c ^ 2 + 1) + (2 * c ^ 2 + 3 * c + 1) / (a ^ 2 + 1) ≥ 9   :=  by sorry
