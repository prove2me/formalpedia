-- Prove2me | Theorems.Thm_TropicalLA_isTropEigen_diagConj
-- name    : TropicalLA.isTropEigen_diagConj
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:53:19.932991+00:00
-- url     : https://prove2.me/theorems/a6c9cb60-46da-46ce-8b40-8bb368c2f1f2
-- title:
--   Diagonal conjugation transports eigenvectors: if `v` is an eigenvector of `A` for
-- statement:
--   Diagonal conjugation transports eigenvectors: if `v` is an eigenvector of `A` for
--   `lam`, then `v + d` is an eigenvector of `diagConj A d` for the same `lam`.
--
--   ```lean
--   theorem TropicalLA.isTropEigen_diagConj{A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ} (d : ι → ℝ)
--       (h : IsTropEigen A lam v) : IsTropEigen (diagConj A d) lam (fun i => v i + d i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalSpectralInvariants.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalSpectralInvariants.lean#L33

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalSpectralInvariants.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalSpectralInvariants
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

open TropicalLA

-- open removed: section is not a namespace

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Diagonal similarity -/

theorem TropicalLA.isTropEigen_diagConj{A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ} (d : ι → ℝ)
    (h : IsTropEigen A lam v) : IsTropEigen (diagConj A d) lam (fun i => v i + d i) := by sorry
