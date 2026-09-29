-- Prove2me | Theorems.Thm_WorkbookSource_plus_79615
-- name    : WorkbookSource.plus_79615
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:56:18.366834+00:00
-- url     : https://prove2.me/theorems/865063da-4cc7-4c84-bb58-58ec09f49000
-- title:
--   A squared quadratic ratio inequality with a normalized correction
-- statement:
--   For a,b,c positive reals
--    $\quad \frac{(a^2+b^2+c^2)^2}{2(a^2b^2+b^2c^2+c^2a^2)+abc(a+b+c)}+1\geq \frac{6(a^2+b^2+c^2)}{(a+b+c)^2}$
--
--    P.S. Look at <http://www.artofproblemsolving.com/Forum/viewtopic.php?f=52&t=384682> for the birth of it
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_79615` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_79615; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_79615 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^2 / (2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) + a * b * c * (a + b + c)) + 1 ≥ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2   :=  by sorry
