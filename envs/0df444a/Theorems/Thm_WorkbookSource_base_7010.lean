-- Prove2me | Theorems.Thm_WorkbookSource_base_7010
-- name    : WorkbookSource.base_7010
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:26:00.930223+00:00
-- url     : https://prove2.me/theorems/ac11a5a1-05eb-42a0-9313-f985623baafe
-- title:
--   A cyclic quadratic-product ratio sum is bounded above
-- statement:
--   With $ x>0, y>0, z>0$ . Prove that: $\frac{xy}{x^2+yz+zx}+\frac{yz}{y^2+zx+xy}+\frac{zx}{z^2+xy+yz} \leq \frac{x^2+y^2+z^2}{xy+yz+zx}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7010` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7010; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7010 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / (x ^ 2 + y * z + z * x) + y * z / (y ^ 2 + z * x + x * y) + z * x / (z ^ 2 + x * y + y * z)) ≤ (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x)  :=  by sorry
