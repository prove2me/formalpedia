-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalSpectralInvariants
-- name    : Algebra_TropicalLinearAlgebra_TropicalSpectralInvariants
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:30:54.364658+00:00
-- url     : https://prove2.me/theorems/d7d47f6e-f598-4abb-be70-29ab69265256
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalSpectralInvariants
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalSpectralInvariants`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalSpectralInvariants.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
/-
# Invariance properties of the max-plus spectral radius

The maximum cycle mean `λ(A)` is the unique tropical eigenvalue of `A`
(`tropEigen_iff_eq_maxCycleMean`).  Here we exploit that characterisation to derive the
three basic invariance/covariance laws of the tropical spectral radius:

* **diagonal similarity**: `λ(D ⊗ A ⊗ D^{-1}) = λ(A)`, where `D` is the tropical diagonal
  matrix with entries `d i` (in max-plus, conjugation by a diagonal matrix just shifts the
  entries by `d i - d j`);
* **powers**: `λ(A^{⊗ k}) = k · λ(A)` — the spectral mapping theorem for monomials;
* **transposition**: `λ(Aᵀ) = λ(A)`, proved combinatorially by reversing cycles.

None of these is definitional: each one is a statement about optima over all cycles of all
lengths, and the first two go through the existence and uniqueness parts of the tropical
Perron–Frobenius theorem.
-/

namespace TropicalLA

open Matrix

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Diagonal similarity -/

/-- Tropical conjugation of `A` by the diagonal matrix with entries `d`:
`(D ⊗ A ⊗ D^{-1}) i j = d i + A i j - d j`. -/
def diagConj (A : Matrix ι ι ℝ) (d : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => d i + A i j - d j



/-! ## Spectral mapping for tropical powers -/


/-! ## Transposition -/




end TropicalLA


