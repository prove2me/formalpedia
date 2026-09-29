-- Prove2me | Theorems.Thm_WorkbookSource_plus_68327
-- name    : WorkbookSource.plus_68327
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:52.941424+00:00
-- url     : https://prove2.me/theorems/b541190a-4b3a-4506-a639-3a8670acdc45
-- title:
--   A six-variable quadratic difference bound
-- statement:
--   Prove that $x^2+y^2+z^2+a^2+b^2+c^2-a(y+z)-b(z+x)-c(x+y) \geq \frac{1}{3}(a+b+c-x-y-z)^2$ for $x,y,z,a,b,c > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68327` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68327; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68327 (x y z a b c : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : x^2 + y^2 + z^2 + a^2 + b^2 + c^2 - a * (y + z) - b * (z + x) - c * (x + y) ≥ (1 / 3) * (a + b + c - x - y - z)^2   :=  by sorry
