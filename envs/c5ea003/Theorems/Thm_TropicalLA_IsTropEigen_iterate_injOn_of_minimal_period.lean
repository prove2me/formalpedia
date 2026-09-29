-- Prove2me | Theorems.Thm_TropicalLA_IsTropEigen_iterate_injOn_of_minimal_period
-- name    : TropicalLA.IsTropEigen.iterate_injOn_of_minimal_period
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:09:08.136367+00:00
-- url     : https://prove2.me/theorems/81bcb9bb-abe0-42fe-baa1-c3855ac387c3
-- title:
--   Points on the minimal-period orbit are pairwise distinct.
-- statement:
--   Points on the minimal-period orbit are pairwise distinct.
--
--   ```lean
--   theorem TropicalLA.IsTropEigen.iterate_injOn_of_minimal_period{f : ι → ι} {y : ι} {p : ℕ}
--       (hp : f^[p] y = y) (hmin : ∀ q, 0 < q → q < p → f^[q] y ≠ y) :
--       Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean#L108

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







omit [Fintype ι] [Nonempty ι] in

theorem TropicalLA.IsTropEigen.iterate_injOn_of_minimal_period{f : ι → ι} {y : ι} {p : ℕ}
    (hp : f^[p] y = y) (hmin : ∀ q, 0 < q → q < p → f^[q] y ≠ y) :
    Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) := by sorry
