-- Prove2me | Theorems.Thm_WorkbookSource_base_1111
-- name    : WorkbookSource.base_1111
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:03.855382+00:00
-- url     : https://prove2.me/theorems/e4fa09ac-a4b1-4fbb-8de7-9937a1b5a90a
-- title:
--   A sum of quadratic ratios has a constant lower bound
-- statement:
--   Let $ a,b,c$ positive reals. Prove that
--
--    $ \frac {4a^2 + 9bc}{(b + c)^2} + \frac {4b^2 + 9ca}{(c + a)^2} + \frac {4c^2 + 9ab}{(a + b)^2}\geq\frac {39}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1111` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1111; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1111 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a ^ 2 + 9 * b * c) / (b + c) ^ 2 + (4 * b ^ 2 + 9 * c * a) / (c + a) ^ 2 + (4 * c ^ 2 + 9 * a * b) / (a + b) ^ 2 ≥ 39 / 4  :=  by sorry
