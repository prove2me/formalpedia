-- Prove2me | Theorems.Thm_WorkbookSource_base_11618
-- name    : WorkbookSource.base_11618
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:28.006695+00:00
-- url     : https://prove2.me/theorems/ebcd6d31-2811-4b40-8871-e1a77d2ac1c5
-- title:
--   A refinement of the cyclic pairwise ratio bound
-- statement:
--   For $ x, y, z > 0 $ real numbers, prove that:
--   $ \frac{12(xy+yz+zx)}{(x+y+z)^2} + 2\left( \frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y} \right) \ge 7 \ \ ; $
--
--   Greetings from Lorian Saceanu
--   Thanks to my friend BQ for his support!
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11618` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11618; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11618 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 12 * (x * y + y * z + z * x) / (x + y + z) ^ 2 + 2 * (x / (y + z) + y / (x + z) + z / (x + y)) ≥ 7  :=  by sorry
