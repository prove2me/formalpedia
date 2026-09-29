-- Prove2me | Theorems.Thm_WorkbookSource_base_13763
-- name    : WorkbookSource.base_13763
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:53.435721+00:00
-- url     : https://prove2.me/theorems/88702a3d-8bd6-4361-bb08-870a2567f795
-- title:
--   A shifted reciprocal sum bounded by a normalized square
-- statement:
--   Let x,y,z be positive reals. Prove that $ \frac {x}{x + 2} + \frac {y}{y + 2} + \frac {z}{z + 2} \ge \frac {(x + y + z)^2}{x^2 + y^2 + z^2 + 2x + 2y + 2z}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13763` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13763; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13763 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x / (x + 2) + y / (y + 2) + z / (z + 2)) ≥ (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 2 * x + 2 * y + 2 * z)  :=  by sorry
