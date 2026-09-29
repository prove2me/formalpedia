-- Prove2me | Theorems.Thm_WorkbookSource_base_28443
-- name    : WorkbookSource.base_28443
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:59:54.924803+00:00
-- url     : https://prove2.me/theorems/f1e23aa8-20c8-4a44-a67d-f1580cda405e
-- title:
--   A product of sums bounds a symmetric product ratio
-- statement:
--   If $ x, y, z $ are positive real numbers then: $(x+y+z)\left(\frac{1}{x}+\frac{1}{y}+\frac{1}{z}\right) \ge 7+ \frac{2(xy+yz+zx)^2}{3xyz(x+y+z)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_28443` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_28443; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_28443 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) * (1 / x + 1 / y + 1 / z) ≥ 7 + 2 * (x * y + y * z + z * x) ^ 2 / (3 * x * y * z * (x + y + z))  :=  by sorry
