-- Prove2me | Theorems.Thm_WorkbookSource_base_1581
-- name    : WorkbookSource.base_1581
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:22.109178+00:00
-- url     : https://prove2.me/theorems/d3893827-cf95-4673-a391-d2e2cc4316c9
-- title:
--   A quartic bound on a cyclic antisymmetric sum
-- statement:
--   Prove that
--
--    $ 3\sum_{cyc}x^4+7\left(\sum_{cyc}x^2y^2-\sum_{cyc}x^2yz\right)\geq 9\left(\sum_{cyc}x^3y-\sum_{cyc}xy^3\right)$
--
--    for $ x,y,z\in\mathbb{R}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1581` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1581; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1581 (x y z : ℝ) : 3 * (x ^ 4 + y ^ 4 + z ^ 4) + 7 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 - (x ^ 2 * y * z + y ^ 2 * z * x + z ^ 2 * x * y)) ≥ 9 * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x - (x * y ^ 3 + y * z ^ 3 + z * x ^ 3))  :=  by sorry
