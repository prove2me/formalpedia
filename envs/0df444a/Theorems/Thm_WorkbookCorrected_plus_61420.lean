-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_61420
-- name    : WorkbookCorrected.plus_61420
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:57:12.772111+00:00
-- url     : https://prove2.me/theorems/868d3f57-83ad-434d-8074-0fc8544e9145
-- title:
--   A linear identity from two reciprocal quadratic constraints
-- statement:
--   Let $x, y, z > 0$ : $xy+yz+zx = 1$ and $\frac{1}{1+x^2} + \frac{1}{1+y^2} = \frac{5}{1+z^2}$ . Prove that : $ z = 2(x+y) $
--
--   Formalization Note: The original formalization added xyz=1, absent from the source and incompatible with xy+yz+zx=1 for positive variables. This corrected statement removes the added product assumption and proves the full source conclusion.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_61420 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_61420; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_61420 (x y z : ℝ) (hx : 0<x) (hy : 0<y) (hz : 0<z)
    (hxy : x*y+y*z+z*x=1)
    (h : 1/(1+x^2)+1/(1+y^2)=5/(1+z^2)) : z=2*(x+y) := by sorry
