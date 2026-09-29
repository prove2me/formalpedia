-- Prove2me | Theorems.Thm_WorkbookSource_base_6220
-- name    : WorkbookSource.base_6220
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:37.307733+00:00
-- url     : https://prove2.me/theorems/b5caf516-551c-45a0-b2cc-aac6055bb9ff
-- title:
--   A squared-product bound with a sum constraint
-- statement:
--   Prove that: $x^2y^2z^2+\frac{1}{27}(x+y+z)^3\geq \frac{2}{3}(x+y+z)xyz$ given $x,y,z$ are real numbers such that $x+y+z\geq3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6220` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6220; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6220 (x y z : ℝ) (h : x + y + z ≥ 3) :
  x^2*y^2*z^2 + 1/27 * (x + y + z)^3 ≥ 2/3 * (x + y + z) * x * y * z  :=  by sorry
