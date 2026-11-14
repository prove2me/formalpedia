-- Prove2me | Theorems.Thm_det_mul_det_updateCol
-- name    : det_mul_det_updateCol
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T01:59:15.755034+00:00
-- url     : https://prove2.me/theorems/79c65d74-ebb3-43cb-bc3d-6add12a9abad
-- title:
--   Division-free determinant identity for column replacement
-- statement:
--   Let $R$ be a commutative ring, let $I$ be a finite index set, and let $A,B\in R^{I\times I}$. Fix $j\in I$ and a vector $v\in R^I$. Write $A[i\leftarrow v]$ for column replacement, and write $A_i$ for the $i$th column of $A$. Then
--
--   $$
--   \det(A)\det\bigl(B[j\leftarrow v]\bigr)
--   =\sum_{i\in I}\det\bigl(A[i\leftarrow v]\bigr)\det\bigl(B[j\leftarrow A_i]\bigr).
--   $$
--
--   The identity requires neither an inverse of $A$ nor a nonzero determinant. It provides a division-free way to transfer Cramer's vector identity through a determinant that is linear in one column.
-- source:
--   An abstract consequence of Cramer's vector identity and determinant linearity. Mathlib at revision c5ea00351c28e24afc9f0f84379aa41082b1188f, LinearAlgebra/Matrix/Adjugate.lean, Matrix.mulVec_cramer (line 284) and Matrix.cramer / Matrix.cramer_apply (lines 94–98): https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/LinearAlgebra/Matrix/Adjugate.lean#L276-L285 . This is the division-free scalar identity derived from those results, not an additional claim about an invertible matrix.

import Mathlib.LinearAlgebra.Matrix.Adjugate
open scoped BigOperators

theorem det_mul_det_updateCol
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A B : Matrix ι ι R) (j : ι) (v : ι → R) :
    A.det * (B.updateCol j v).det =
      ∑ i, (A.updateCol i v).det *
        (B.updateCol j (fun r => A r i)).det := by sorry
