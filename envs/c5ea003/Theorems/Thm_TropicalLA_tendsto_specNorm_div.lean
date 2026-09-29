-- Prove2me | Theorems.Thm_TropicalLA_tendsto_specNorm_div
-- name    : TropicalLA.tendsto_specNorm_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:57:16.894347+00:00
-- url     : https://prove2.me/theorems/c79a3b67-1be7-47a5-8b93-aeeffaf98a9b
-- title:
--   Tropical Gelfand formula.
-- statement:
--   **Tropical Gelfand formula.**  The normalised largest entry of the tropical powers
--   of `A` converges to the maximum cycle mean of `A`.
--
--   ```lean
--   theorem TropicalLA.tendsto_specNorm_div(A : Matrix ι ι ℝ) :
--       Tendsto (fun m : ℕ => specNorm A m / (m + 1)) atTop (𝓝 (maxCycleMean A)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalGelfand.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalGelfand.lean#L145

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalGelfand.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# A tropical Gelfand formula: growth rate of matrix powers

Classically the spectral radius of a matrix is the limit of `‖A^m‖^{1/m}`.  In the
max-plus world exponentiation becomes multiplication, and the statement becomes

  `‖A^{⊗ m}‖ / m → λ(A)`,

where `‖·‖` is the largest entry and `λ(A)` is the maximum cycle mean.  This file
proves the sharp two-sided form: the largest entry of `A^{⊗(m+1)}` differs from
`(m+1)·λ` by at most the *spread* `max v - min v` of a tropical eigenvector,
uniformly in `m`, hence the normalised growth rate converges to `λ`.

The bridge is that the eigenvector is preserved by the tropical action:
`A^{⊗(m+1)} ⊗ v = ((m+1)·λ) ⊗ v` (`IsTropEigen.tmulVec_tpow`).
-/

open TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]


open IsTropEigen

variable {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}




variable (A : Matrix ι ι ℝ)


variable {A}

theorem TropicalLA.tendsto_specNorm_div(A : Matrix ι ι ℝ) :
    Tendsto (fun m : ℕ => specNorm A m / (m + 1)) atTop (𝓝 (maxCycleMean A)) := by sorry
