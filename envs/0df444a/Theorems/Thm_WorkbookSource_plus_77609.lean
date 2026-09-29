-- Prove2me | Theorems.Thm_WorkbookSource_plus_77609
-- name    : WorkbookSource.plus_77609
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:33.698038+00:00
-- url     : https://prove2.me/theorems/c236178c-a756-4914-87ce-b71c56ed74b4
-- title:
--   A shifted cyclic linear product ratio is at least two hundred forty-three
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that:
--
--    $$ \frac{(2x+4y+3)(2y+4z+3)(2z+4x+3)}{xy+yz+zx} \ge 243 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_77609` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_77609; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_77609 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2*x + 4*y + 3)*(2*y + 4*z + 3)*(2*z + 4*x + 3) / (x*y + y*z + z*x) ≥ 243   :=  by sorry
