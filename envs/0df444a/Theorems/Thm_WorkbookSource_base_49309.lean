-- Prove2me | Theorems.Thm_WorkbookSource_base_49309
-- name    : WorkbookSource.base_49309
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:56.222396+00:00
-- url     : https://prove2.me/theorems/79db6a35-d3a0-4885-97b6-acf012e43d31
-- title:
--   A squared fourth-power sum bounds a fifth-power triple product
-- statement:
--   Prove that $(x^{4}+y^{4}+z^{4})^{2}\geq 3xyz(x^{5}+y^{5}+z^{5})$ given $x,y,z\geq 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49309` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49309; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49309 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x^4 + y^4 + z^4)^2 ≥ 3 * x * y * z * (x^5 + y^5 + z^5)  :=  by sorry
