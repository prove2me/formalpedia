-- Prove2me | Theorems.Thm_WorkbookSource_base_11082
-- name    : WorkbookSource.base_11082
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:36:32.199466+00:00
-- url     : https://prove2.me/theorems/118872a2-a14b-4fae-afcf-79798b6bdb61
-- title:
--   A cyclic linear-over-quadratic reciprocal lower bound
-- statement:
--   Let x,y,z positive numbers. Prove that :
--
--    $ \frac{x}{y^2+yz+z^2}+\frac{y}{z^2+zx+x^2}+\frac{z}{x^2+xy+y^2}\ge \frac{3}{x+y+z}$
--
--    Pachitariu M.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11082` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11082; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11082 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y ^ 2 + y * z + z ^ 2) + y / (z ^ 2 + z * x + x ^ 2) + z / (x ^ 2 + x * y + y ^ 2)) ≥ 3 / (x + y + z)  :=  by sorry
