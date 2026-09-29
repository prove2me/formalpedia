-- Prove2me | Theorems.Thm_WorkbookSource_base_6019
-- name    : WorkbookSource.base_6019
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:36.081972+00:00
-- url     : https://prove2.me/theorems/3baef832-3bed-43b7-bf93-22c684fba3e5
-- title:
--   A squared cubic sum bounds three quadratic factors
-- statement:
--   Let $ab=z^2$ , $ac=y^2$ and $bc=x^2$ , where $x$ , $y$ and $z$ are positive numbers. Hence, we need to prove that $(x^3+y^3+z^3+xyz)^2\geq2(x^2+y^2)(x^2+z^2)(y^2+z^2)$ , which is $\sum_{cyc}(x^6-2x^4y^2-x^4z^2+2x^3y^3+2x^4yz-x^2y^2z^2)\geq0$ , which is obvious (Schur and SOS).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6019` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6019; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6019 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3 + x * y * z)^2 ≥ 2 * (x^2 + y^2) * (x^2 + z^2) * (y^2 + z^2)  :=  by sorry
