-- Prove2me | Theorems.Thm_TropicalLA_IsTropEigen_le_of
-- name    : TropicalLA.IsTropEigen.le_of
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:07:53.179749+00:00
-- url     : https://prove2.me/theorems/837f97f2-c795-444f-b83e-be91282b2686
-- title:
--   The eigenvector inequality `A i j + v j ≤ lam + v i`.
-- statement:
--   The eigenvector inequality `A i j + v j ≤ lam + v i`.
--
--   ```lean
--   theorem TropicalLA.IsTropEigen.le_of(h : IsTropEigen A lam v) (i j : ι) : A i j + v j ≤ lam + v i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean#L35

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

theorem TropicalLA.IsTropEigen.le_of(h : IsTropEigen A lam v) (i j : ι) : A i j + v j ≤ lam + v i := by sorry
