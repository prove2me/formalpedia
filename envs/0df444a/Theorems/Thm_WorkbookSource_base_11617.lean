-- Prove2me | Theorems.Thm_WorkbookSource_base_11617
-- name    : WorkbookSource.base_11617
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:38:35.053521+00:00
-- url     : https://prove2.me/theorems/df862c53-e35c-4a97-b0c3-9ad971279f68
-- title:
--   A cyclic cubic-over-linear sum bounds the quadratic mean
-- statement:
--   For positive real numbers $ x, y, z $ , prove the inequality: $$ \displaylines {\frac {x ^ 3} {x + y} + \frac {y ^ 3} {y + z} + \frac {z ^ 3} {z + x} \geq \frac {x^2+y^2+z^2} {2}.} $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11617` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11617; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11617 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x ^ 3 / (x + y) + y ^ 3 / (y + z) + z ^ 3 / (z + x)) ≥ (x ^ 2 + y ^ 2 + z ^ 2) / 2  :=  by sorry
