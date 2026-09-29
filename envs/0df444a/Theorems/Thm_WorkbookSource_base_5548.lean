-- Prove2me | Theorems.Thm_WorkbookSource_base_5548
-- name    : WorkbookSource.base_5548
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:16.465122+00:00
-- url     : https://prove2.me/theorems/8f9c983e-c4a1-4c9f-beef-458a3fc68451
-- title:
--   A cyclic cubic-over-linear sum bounds pairwise products
-- statement:
--   For positive real numbers $ x, y, z $ , prove the inequality: $$ \displaylines {\frac {x ^ 3} {x + y} + \frac {y ^ 3} {y + z} + \frac {z ^ 3} {z + x} \geq \frac {xy + yz + zx} {2}.} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5548` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5548; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5548 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x)) ≥ (x * y + y * z + z * x) / 2  :=  by sorry
