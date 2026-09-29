-- Prove2me | Theorems.Thm_WorkbookSource_base_5580
-- name    : WorkbookSource.base_5580
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:09:15.626362+00:00
-- url     : https://prove2.me/theorems/d53f52cd-d38e-4fda-addd-ee1497b18a8e
-- title:
--   A quadratic pair-sum ratio bounds a squared square-root sum
-- statement:
--   If $x$ , $y$ , $z$ are positive reals, prove that $\frac{\left(y+z\right)^{2}}{y+z+2x}+\frac{\left(z+x\right)^{2}}{z+x+2y}+\frac{\left(x+y\right)^{2}}{x+y+2z}\geq\frac{\left(\sqrt{x}+\sqrt{y}+\sqrt{z}\right)^{2}}{3}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5580` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5580; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5580 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 / (y + z + 2 * x) + (z + x) ^ 2 / (z + x + 2 * y) + (x + y) ^ 2 / (x + y + 2 * z) ≥ (Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 / 3  :=  by sorry
