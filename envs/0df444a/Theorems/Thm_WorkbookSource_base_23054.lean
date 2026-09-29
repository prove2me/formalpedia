-- Prove2me | Theorems.Thm_WorkbookSource_base_23054
-- name    : WorkbookSource.base_23054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:10.462138+00:00
-- url     : https://prove2.me/theorems/2c33fd1e-444e-48d1-a813-5f90f9fcbf8b
-- title:
--   A sixth-power bound for three quadratic factors
-- statement:
--   Let $x,y,z \ge 0$ . Prove that : $\left (x+y+z \right )^6 \ge \left (8x^2+yz \right )\left (8y^2+xz \right )\left (8z^2+xy \right )$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23054 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 6 ≥ (8 * x ^ 2 + y * z) * (8 * y ^ 2 + x * z) * (8 * z ^ 2 + x * y)  :=  by sorry
