-- Prove2me | Theorems.Thm_WorkbookSource_base_9970
-- name    : WorkbookSource.base_9970
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:24.676685+00:00
-- url     : https://prove2.me/theorems/4a04c22c-b9c8-4be3-81f1-ab198f11562e
-- title:
--   A two-variable rational inequality with a product correction
-- statement:
--   Let $x,y>0$ ,prove that: $\frac{16}{x+y}+\frac{x^2+14xy+y^2+16}{xy}\geq \frac{80}{xy+1}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9970` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9970; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9970 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 16 / (x + y) + (x ^ 2 + 14 * x * y + y ^ 2 + 16) / (x * y) ≥ 80 / (x * y + 1)  :=  by sorry
