-- Prove2me | Theorems.Thm_TropicalLA_IsTropEigen_cycle_le
-- name    : TropicalLA.IsTropEigen.cycle_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:08:31.540985+00:00
-- url     : https://prove2.me/theorems/8911e894-1739-46ad-8e9d-72c86a6d3d57
-- title:
--   Every cycle mean is at most the eigenvalue.
-- statement:
--   **Every cycle mean is at most the eigenvalue.**  For a closed walk
--   `c 0 → c 1 → ⋯ → c m = c 0` the total weight is at most `m · lam`; the eigenvector
--   values telescope away.
--
--   ```lean
--   theorem TropicalLA.IsTropEigen.cycle_le(h : IsTropEigen A lam v) {m : ℕ} {c : ℕ → ι} (hc : c m = c 0) :
--       pathWeight A c m ≤ m * lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean#L44

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalDeterminant
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
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

theorem TropicalLA.IsTropEigen.cycle_le(h : IsTropEigen A lam v) {m : ℕ} {c : ℕ → ι} (hc : c m = c 0) :
    pathWeight A c m ≤ m * lam := by sorry
