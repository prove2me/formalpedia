-- Prove2me | Theorems.Thm_WorkbookRestored_plus_54222
-- name    : WorkbookRestored.plus_54222
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:46:30.910325+00:00
-- url     : https://prove2.me/theorems/d0ed6999-24d9-44bd-b1a0-25f8cfe1374d
-- title:
--   Lean-Workbook Plus 54222: Degree of a polynomial product
-- statement:
--   For polynomials $f,g$ with integer coefficients, $\deg(fg)=\deg f+\deg g$. The zero polynomial has extended degree $-\infty$, represented by Lean's bottom value.
--
--   Source: Lean-Workbook row `lean_workbook_plus_54222` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/87afcd65-4708-46b1-ad91-416dc1505926); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_54222; immutable original Prove2Me node 87afcd65-4708-46b1-ad91-416dc1505926

import Mathlib.Algebra.Polynomial.Degree.Operations

theorem WorkbookRestored.plus_54222 (f g : Polynomial ℤ) : (f * g).degree = f.degree + g.degree   :=  by sorry
