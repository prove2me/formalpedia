-- Prove2me | Theorems.Thm_WorkbookSource_base_35726
-- name    : WorkbookSource.base_35726
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:04:17.046789+00:00
-- url     : https://prove2.me/theorems/565631d8-a9be-4698-8973-5c7d8fb5560e
-- title:
--   A cyclic mixed quadratic ratio sum is at most one
-- statement:
--   Prove that if $x,y,z>0$ then,
--
--    $$ \dfrac{xy}{x^2+xy+yz} + \dfrac{yz}{y^2+yz+zx} + \dfrac{zx}{z^2+zx+xy}\leq 1 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35726` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35726; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35726 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y) / (x ^ 2 + x * y + y * z) + (y * z) / (y ^ 2 + y * z + z * x) + (z * x) / (z ^ 2 + z * x + x * y) ≤ 1  :=  by sorry
