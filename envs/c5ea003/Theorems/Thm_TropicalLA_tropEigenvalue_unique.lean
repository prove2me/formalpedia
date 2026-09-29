-- Prove2me | Theorems.Thm_TropicalLA_tropEigenvalue_unique
-- name    : TropicalLA.tropEigenvalue_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:45:37.702173+00:00
-- url     : https://prove2.me/theorems/a472c4e1-6f71-4f39-8baa-fb7dd7747526
-- title:
--   Uniqueness of the tropical eigenvalue.
-- statement:
--   **Uniqueness of the tropical eigenvalue.**  Any two eigenvalues of the same
--   max-plus matrix coincide — both equal the maximum cycle mean.
--
--   ```lean
--   theorem TropicalLA.tropEigenvalue_unique{A : Matrix ι ι ℝ} {lam₁ lam₂ : ℝ} {v₁ v₂ : ι → ℝ}
--       (h₁ : IsTropEigen A lam₁ v₁) (h₂ : IsTropEigen A lam₂ v₂) : lam₁ = lam₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean#L176

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
/-
# Tropical eigenvalues and the max-plus Perron–Frobenius theorem

An eigenpair of a max-plus matrix `A` (finite real entries) is a pair `(lam, v)`
with `A ⊗ v = lam ⊗ v`, i.e.

  `max_j (A i j + v j) = lam + v i`  for every `i`.

Main results of this file:

* `IsTropEigen.cycle_le` : every closed walk (cycle) of `A` has weight at most
  `length · lam` — an eigenvalue dominates all cycle means;
* `IsTropEigen.exists_critical_cycle` : some *simple* cycle attains the mean `lam`
  exactly (the critical cycle), obtained from the argmax function of the eigenvector
  by a minimal-period pigeonhole argument;
* `IsTropEigen.isGreatest_cycleMean` : **tropical Perron–Frobenius (spectral part)** —
  `lam` is the *maximum cycle mean* of `A`, and hence
* `tropEigenvalue_unique` : a max-plus matrix has at most one eigenvalue.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]


open IsTropEigen

variable {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}

theorem TropicalLA.tropEigenvalue_unique{A : Matrix ι ι ℝ} {lam₁ lam₂ : ℝ} {v₁ v₂ : ι → ℝ}
    (h₁ : IsTropEigen A lam₁ v₁) (h₂ : IsTropEigen A lam₂ v₂) : lam₁ = lam₂ := by sorry
