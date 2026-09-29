-- Prove2me | Theorems.Thm_lean_workbook_plus_29913
-- name    : lean_workbook_plus_29913
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a911136f-70d5-4900-abb6-8f42530dfd08
-- statement:
--   Show that the determinant of the Vandermonde matrix $ \left(\begin{array}{ccc}1 & a & a^2 \ 1 & b & b^2 \ 1 & c & c^2\end{array}\right)$ is $(b-a)(c-a)(c-b)$ without computing the determinant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29913 {R : Type*} [CommRing R] (a b c : R) :
  Matrix.det (![![(1 : R), a, a^2],![(1 : R), b, b^2],![(1 : R), c, c^2]]) =
    (b - a) * (c - a) * (c - b)   :=  by sorry
