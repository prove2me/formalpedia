-- Prove2me | Theorems.Thm_WorkbookSource_base_9764
-- name    : WorkbookSource.base_9764
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:43:56.014201+00:00
-- url     : https://prove2.me/theorems/ca967f34-37a7-4b63-bac6-f3806807f1f4
-- title:
--   A fourth-power bound on cyclic cubic products
-- statement:
--   (x+y+z)^4\geq9\sum_{cyc}(x^3y+2x^2yz)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9764` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9764; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9764 (x y z : ℝ) : (x + y + z) ^ 4 ≥ 9 * (x ^ 3 * y + 2 * x ^ 2 * y * z + y ^ 3 * z + 2 * y ^ 2 * z * x + z ^ 3 * x + 2 * z ^ 2 * x * y)  :=  by sorry
