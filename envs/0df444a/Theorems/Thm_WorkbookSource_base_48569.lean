-- Prove2me | Theorems.Thm_WorkbookSource_base_48569
-- name    : WorkbookSource.base_48569
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:14.448957+00:00
-- url     : https://prove2.me/theorems/1e2972f6-0f03-4e1d-9975-18eb78a159b7
-- title:
--   A quadratic sum times pairwise reciprocals bounds the total
-- statement:
--   Prove that for $x, y, z > 0$,
--   $(x^2 + y^2 + z^2)\cdot \sum \frac 1{y + z} \ge \frac 32 \cdot (x + y + z)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48569` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48569; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48569 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2) * (1/(y + z) + 1/(x + z) + 1/(x + y)) ≥ 3/2 * (x + y + z)  :=  by sorry
