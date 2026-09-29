-- Prove2me | Theorems.Thm_WorkbookSource_base_48397
-- name    : WorkbookSource.base_48397
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:43:35.104721+00:00
-- url     : https://prove2.me/theorems/f5a61caa-5b8f-4e30-9a3f-daa081674355
-- title:
--   A four-variable product bound at fixed squared norm
-- statement:
--   $x^2+y^2+z^2+t^2=4 \implies xyzt \le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48397` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48397; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48397 (x y z t : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 + t ^ 2 = 4) :
  x * y * z * t ≤ 1  :=  by sorry
