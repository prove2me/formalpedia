-- Prove2me | Theorems.Thm_QuadraticFormsNumberFields_anisotropic_iff_of_isometryEquiv
-- name    : QuadraticFormsNumberFields.anisotropic_iff_of_isometryEquiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:50:43.714464+00:00
-- url     : https://prove2.me/theorems/71c798c7-4830-4d79-835d-42a19fcf7d3d
-- title:
--   An isometric equivalence preserves anisotropy in both directions.
-- statement:
--   An isometric equivalence preserves anisotropy in both directions.
--
--   ```lean
--   theorem QuadraticFormsNumberFields.anisotropic_iff_of_isometryEquiv    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
--       (e : Q.IsometryEquiv Q') : Q.Anisotropic ↔ Q'.Anisotropic := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QuadraticFormsNumberFields.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QuadraticFormsNumberFields.lean#L34

-- Thm stub generated from Algebra/QuadraticFormsNumberFields.lean
import Mathlib
import Definitions.Def_Algebra_QuadraticFormsNumberFields
/-
# Quadratic forms over number fields: local-global infrastructure

This file develops kernel-checked algebraic consequences needed by a future full
place-theoretic Hasse--Minkowski theorem.  It uses Mathlib's `QuadraticForm`,
`QuadraticMap.Anisotropic`, isometric equivalences, and scalar extension.

The actual construction of all completions of a number field and the arithmetic
reciprocity theorem are not currently part of Mathlib.  The results here therefore
establish unconditional invariance and scalar-extension foundations on which a
future place-theoretic Hasse--Minkowski theorem can be built.
-/


open scoped TensorProduct

open QuadraticFormsNumberFields

open QuadraticMap

noncomputable section


variable {K L V W : Type*}


variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

theorem QuadraticFormsNumberFields.anisotropic_iff_of_isometryEquiv    {Q : QuadraticForm K V} {Q' : QuadraticForm K W}
    (e : Q.IsometryEquiv Q') : Q.Anisotropic ↔ Q'.Anisotropic := by sorry
