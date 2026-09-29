-- Prove2me | Theorems.Thm_AlternatingAdjacentSum_matrix_power_recurrence
-- name    : AlternatingAdjacentSum.matrix_power_recurrence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:31:43.368986+00:00
-- url     : https://prove2.me/theorems/a7f3c330-5636-45f3-91c2-42afcc4d3f8b
-- title:
--   Every matrix power satisfies the characteristic recurrence.
-- statement:
--   Every matrix power satisfies the characteristic recurrence.
--
--   ```lean
--   theorem AlternatingAdjacentSum.matrix_power_recurrence{R : Type*} [CommRing R]
--       (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
--       M ^ (n + 2) = (Matrix.trace M) • M ^ (n + 1) - (Matrix.det M) • M ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AlternatingAdjacentSum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AlternatingAdjacentSum.lean#L53

-- Thm stub generated from Cryptography/AlternatingAdjacentSum.lean
import Mathlib
import Definitions.Def_Cryptography_AlternatingAdjacentSum
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Alternating adjacent-sum transfer matrices

This file formalizes the algebraic mechanism behind the parity split for
period-two adjacent-sum constraints.  A bound `b` is represented by its finite
zero-one compatibility matrix.  Pairing two successive bounds gives a single
transfer matrix.  Cayley--Hamilton in dimension two then shows that open
boundary counts and both cyclic parity classes obey the same second-order
recurrence, hence have a common quadratic denominator.
-/

open Finset BigOperators

open AlternatingAdjacentSum

theorem AlternatingAdjacentSum.matrix_power_recurrence{R : Type*} [CommRing R]
    (M : Matrix (Fin 2) (Fin 2) R) (n : ℕ) :
    M ^ (n + 2) = (Matrix.trace M) • M ^ (n + 1) - (Matrix.det M) • M ^ n := by sorry
