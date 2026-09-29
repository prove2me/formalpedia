-- Prove2me | Theorems.Thm_TropicalLA_maxCycleMean_submatrix_le
-- name    : TropicalLA.maxCycleMean_submatrix_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:54:03.273979+00:00
-- url     : https://prove2.me/theorems/74403969-4356-4735-b755-f4b93492fb01
-- title:
--   Monotonicity of the spectral radius under (principal) submatrices.
-- statement:
--   **Monotonicity of the spectral radius under (principal) submatrices.**  A closed walk of
--   the submatrix indexed by `f` is a closed walk of `A` with the same weight, hence its mean is
--   dominated by the maximum cycle mean of `A`.  Taking `f` to be the inclusion of a nonempty
--   subset gives monotonicity under principal submatrices.
--
--   ```lean
--   theorem TropicalLA.maxCycleMean_submatrix_le(A : Matrix ι ι ℝ) {J : Type*} [Fintype J] [Nonempty J]
--       (f : J → ι) : maxCycleMean (A.submatrix f f) ≤ maxCycleMean A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalNewtonPolygon.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalNewtonPolygon.lean#L29

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalNewtonPolygon.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCharPoly
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# The tropical Newton polygon: the spectral radius is the largest tropical root

`TropicalCharPoly.lean` shows that a tropical eigenvalue is *a* corner of the tropical
characteristic polynomial `p_A(x) = max_k (c_k + (n−k)·x)`.  Conjecture **C2** of
`FUTURE_DIRECTIONS.md` asks for the whole corner locus.  This file settles the extremal
part of that conjecture and the coefficient formula behind it:

* `maxCycleMean_submatrix_le` — the max-plus spectral radius is monotone under principal
  submatrices (every cycle of a principal submatrix is a cycle of the whole matrix);
* `isGreatest_charCoeff_div` — **coefficient formula for the spectral radius**:
  `λ(A) = max_{1 ≤ k ≤ n} c_k / k`, the largest slope of the Newton polygon of `p_A`;
* `isGreatest_tropicalRoot` — **`λ(A)` is exactly the largest tropical root of the
  characteristic polynomial**: it is a corner (by `eigen_isTropicalRoot`), and beyond it
  the degree-`0` monomial `n·x` strictly dominates every other monomial, so no larger
  corner exists.

Together these say that the top of the Newton polygon of `p_A` is the tropical spectrum,
which is the extremal case of the principal-submatrix description conjectured in C2.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in

theorem TropicalLA.maxCycleMean_submatrix_le(A : Matrix ι ι ℝ) {J : Type*} [Fintype J] [Nonempty J]
    (f : J → ι) : maxCycleMean (A.submatrix f f) ≤ maxCycleMean A := by sorry
