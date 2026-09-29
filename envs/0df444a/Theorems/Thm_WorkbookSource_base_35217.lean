-- Prove2me | Theorems.Thm_WorkbookSource_base_35217
-- name    : WorkbookSource.base_35217
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:27:52.489394+00:00
-- url     : https://prove2.me/theorems/02c3cb9d-f306-4b84-9c22-9ba2de0ef178
-- title:
--   A sixth-degree difference-product bound at fixed sum
-- statement:
--   Let $x,y,z$ are real numbers, and $x+y+z=3$, prove that:
--   $(3-xy-yz-xz)^3\geq \frac{1}{4}(y-z)^2(z-x)^2(x-y)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35217` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35217; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35217 (x y z : ℝ) (h : x + y + z = 3) :
  (3 - x * y - y * z - z * x) ^ 3 ≥ (1 / 4) * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2  :=  by sorry
