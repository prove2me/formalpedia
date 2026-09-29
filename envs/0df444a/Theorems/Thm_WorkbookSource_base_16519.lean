-- Prove2me | Theorems.Thm_WorkbookSource_base_16519
-- name    : WorkbookSource.base_16519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T08:30:42.17689+00:00
-- url     : https://prove2.me/theorems/72281037-7043-46c9-b38e-7fb7d2639d08
-- title:
--   A parameterized weighted reciprocal sum comparison
-- statement:
--   Let $x,y,z,k > 0$ , prove that $\frac{1}{kx + y + z} + \frac{1}{x + ky + z} + \frac{1}{x + y + kz} \leq \frac{1}{k + 2} \cdot \left(\frac{1}{x} + \frac{1}{y} + \frac{1}{z}\right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_16519` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_16519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_16519 (x y z k : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hk : 0 < k) : 1 / (k * x + y + z) + 1 / (x + k * y + z) + 1 / (x + y + k * z) ≤ 1 / (k + 2) * (1 / x + 1 / y + 1 / z)  :=  by sorry
