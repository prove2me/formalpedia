-- Prove2me | Theorems.Thm_WorkbookSource_plus_73339
-- name    : WorkbookSource.plus_73339
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:45:39.16476+00:00
-- url     : https://prove2.me/theorems/e597f85f-f1ad-40f3-a9f1-20e981f4370d
-- title:
--   An eighth-power bound for pairwise symmetric products
-- statement:
--   Let $x\geq0,$ $y\geq0,$ $z\geq0.$ Prove that $(x+y+z)^{8}\geq243(xy+xz+yz)^{2}(x^{2}y^{2}+x^{2}z^{2}+y^{2}z^{2}).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73339` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73339; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73339 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 8 ≥ 243 * (x * y + x * z + y * z) ^ 2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)   :=  by sorry
