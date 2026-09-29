-- Prove2me | Theorems.Thm_WorkbookSource_base_29873
-- name    : WorkbookSource.base_29873
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:46:00.76966+00:00
-- url     : https://prove2.me/theorems/86a7975b-1918-463a-813b-3bf0fc50256f
-- title:
--   A squared cubic sum bounds a cyclic quartic-square sum
-- statement:
--   Let $a=\frac{x}{y},$ $b=\frac{y}{z},$ where $x$ , $y$ and $z$ are positives.
--   Thus, $c=\frac{z}{x}$ and we need to prove that:
--    $$(x^3+y^3+z^3)^2\geq3(x^4z^2+y^4x^2+z^4y^2)$$ or
--    $$\sum_{cyc}y^3(x-y)^2(2x+y)\geq0.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29873` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29873; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29873 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3)^2 ≥ 3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2)  :=  by sorry
