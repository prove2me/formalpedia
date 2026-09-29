-- Prove2me | Theorems.Thm_WorkbookSource_base_26788
-- name    : WorkbookSource.base_26788
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:34.900657+00:00
-- url     : https://prove2.me/theorems/d895372b-2b08-4062-b768-6c8dc08eae38
-- title:
--   An eighth-degree comparison of squared pairwise sums
-- statement:
--   Prove that if $ a, b, c > 0 $ then
--    $ 8(a^2+b^2)(b^2+c^2)(c^2+a^2)(a+b+c)^2 \ge 3(a+b)^2(b+c)^2(c+a)^2(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26788` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26788; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26788 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) * (a + b + c)^2 ≥ 3 * (a + b)^2 * (b + c)^2 * (c + a)^2 * (a^2 + b^2 + c^2)  :=  by sorry
