-- Prove2me | Theorems.Thm_Knot_Khovanov_enhancement_state_sum
-- name    : Knot.Khovanov.enhancement_state_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:30:34.138119+00:00
-- url     : https://prove2.me/theorems/618298d7-992d-4a0f-b1d8-fb48f673a644
-- title:
--   Summing the quantum monomial over all binary enhancements of `m` circles
-- statement:
--   Summing the quantum monomial over all binary enhancements of `m` circles
--   produces the `m`-th power of the quantum dimension `q + q⁻¹`.
--
--   ```lean
--   theorem Knot.Khovanov.enhancement_state_sum(m : ℕ) :
--       ∑ e : Fin m → Bool, T (enhancementDegree e) =
--         (T 1 + T (-1) : LaurentPolynomial ℤ) ^ m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/KnotTheory/KhovanovCategorification.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/KnotTheory/KhovanovCategorification.lean#L77

-- Thm stub generated from Geometry/KnotTheory/KhovanovCategorification.lean
import Mathlib
import Definitions.Def_Geometry_KnotTheory_Defs
import Definitions.Def_Geometry_KnotTheory_KhovanovCategorification
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/

/-!
# The graded Euler state sum underlying Khovanov homology

This file formalizes the decategorification calculation for an arbitrary link
diagram.  A Khovanov generator consists of a smoothing state together with a
choice of one of the two quantum basis vectors on every resulting circle.  The
main theorem proves that the graded Euler sum of these generators is the
corresponding Jones state sum.
-/

open Knot.Khovanov

open Finset LaurentPolynomial

theorem Knot.Khovanov.enhancement_state_sum(m : ℕ) :
    ∑ e : Fin m → Bool, T (enhancementDegree e) =
      (T 1 + T (-1) : LaurentPolynomial ℤ) ^ m := by sorry
