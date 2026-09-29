-- Prove2me | Theorems.Thm_PGLQuotient_abel_succ
-- name    : PGLQuotient.abel_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:44:14.68957+00:00
-- url     : https://prove2.me/theorems/8c68a06d-ba7d-4f00-a891-6842cb1fa78f
-- title:
--   The generic term of the Abel summation.
-- statement:
--   The generic term of the Abel summation.
--
--   ```lean
--   theorem PGLQuotient.abel_succ{m i : ℕ} (hi : i ≤ m) (j : ℕ) :
--       q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j)
--         = q ^ (i + 1) * (q ^ (m + 1) - 1) *
--           (Gpoly q m i * Jfac q (m - i) (j + 1)
--             - Gpoly q m (i + 1) * Jfac q (m - (i + 1)) (j + 1)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PGLQuotient/VolumeAlgebra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PGLQuotient/VolumeAlgebra.lean#L144

-- Thm stub generated from Algebra/PGLQuotient/VolumeAlgebra.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VolumeAlgebra

/-!
# The algebraic core of the general-rank vertex volume

This file contains the purely algebraic input for the closed product form of the vertex volume
of the standard arithmetic quotient of `PGL_d(F_q((t^{-1})))` in **arbitrary rank**.

The building-theoretic side (see `Algebra.PGLQuotient.TwistedWeight` and
`Algebra.PGLQuotient.VertexVolumeGeneral`) produces a two-parameter family of *twisted masses*
`M(n,c,j)` (rank `n+1`, twist parameters `c` and `j`) satisfying a row-peeling recursion.  The
solution of that recursion is

`M(n,c,j) = NumV q n c j / DenV q n c j`,

where

* `NumV q n c j = ∑_{i=0}^{n} q^{ci} (∏_{k<i} (q^{n-k}-1)) (∏_{s<n-i}(q^{s+1+j}-1))`,
* `DenV q n c j = (∏_{s<n+1}(q^{s+1+j}-1)) (∏_{k<n}(q^{k+1}-1)) (∏_{k<n}(q^{c+k+1}-1))`.

The main result here is the **cut-set recursion** `NumV_rec`:

`q^{m+1} · NumV q (m+1) c j = (q^{m+1}-1)(q^{c+1}-1) · NumV q m (c+1) (j+1) + Jfac q (m+1) (j+1)`,

proved by an Abel summation whose term-by-term input is a pair of product identities.
Specialising `c = j = 0` collapses `NumV` to `(n+1)·Pfac q n`, which is what produces the
closed product form `d/(P(d)P(d-1))` of the vertex volume.
-/

open PGLQuotient

open Finset


variable (q : ℝ)







variable {q}

theorem PGLQuotient.abel_succ{m i : ℕ} (hi : i ≤ m) (j : ℕ) :
    q ^ (m + 1) * (Gpoly q (m + 1) (i + 1) * Jfac q (m + 1 - (i + 1)) j)
      = q ^ (i + 1) * (q ^ (m + 1) - 1) *
        (Gpoly q m i * Jfac q (m - i) (j + 1)
          - Gpoly q m (i + 1) * Jfac q (m - (i + 1)) (j + 1)) := by sorry
