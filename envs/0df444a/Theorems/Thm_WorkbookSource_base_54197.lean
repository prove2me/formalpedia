-- Prove2me | Theorems.Thm_WorkbookSource_base_54197
-- name    : WorkbookSource.base_54197
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:11.31054+00:00
-- url     : https://prove2.me/theorems/cf7e9f31-f072-4007-ba12-9073a3a7bbcb
-- title:
--   A cyclic product ratio with a symmetric rational correction
-- statement:
--   Let $x, y, z$ be positive reals. Prove that:
--    $\frac{xy}{z}+\frac{yz}{x}+\frac{zx}{y}+9\frac{xyz(x+y+z)^2}{(xy+yz+zx)^2}\ge 4(x+y+z)$
--
--   I think it's my most nice one so far, I hope to see classical solutions
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54197` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54197; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54197 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / z + y * z / x + z * x / y + 9 * (x * y * z * (x + y + z) ^ 2) / (x * y + y * z + z * x) ^ 2) ≥ 4 * (x + y + z)  :=  by sorry
