-- Prove2me | Definitions.Def_Algebra_QuadraticFormsNumberFields
-- name    : Algebra_QuadraticFormsNumberFields
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:53:49.590859+00:00
-- url     : https://prove2.me/theorems/2966afa9-990a-47df-94fd-49fa3a710c6d
-- title:
--   Aether Catalog definitions — Algebra_QuadraticFormsNumberFields
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QuadraticFormsNumberFields`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QuadraticFormsNumberFields.lean by skeleton subtraction
import Mathlib
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

namespace QuadraticFormsNumberFields

open QuadraticMap

noncomputable section

local instance invertibleTwoOfCharZero
    (F : Type*) [Field F] [CharZero F] : Invertible (2 : F) :=
  invertibleOfNonzero (by norm_num)

variable {K L V W : Type*}

section Isometry

variable [Field K] [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]



end Isometry

section ScalarExtension

variable [Field K] [Field L] [Algebra K L]
variable [Invertible (2 : K)]
variable [AddCommGroup V] [Module K V]



end ScalarExtension

section NumberFields

variable [Field K] [NumberField K]
variable [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V]



end NumberFields

end

end QuadraticFormsNumberFields


