-- Prove2me | Theorems.Thm_TropicalLA_IsTropEigen_exists_critical_cycle
-- name    : TropicalLA.IsTropEigen.exists_critical_cycle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T16:28:23.19081+00:00
-- url     : https://prove2.me/theorems/db5d03bb-0a81-40fb-b3a1-44990d07b10b
-- title:
--   Existence of a critical cycle.
-- statement:
--   **Existence of a critical cycle.**  If `lam` is an eigenvalue, some closed walk
--   has mean weight exactly `lam`; moreover it can be taken *simple*: its `p` vertices
--   `y, f y, …, f^{p-1} y` are pairwise distinct.
--
--   ```lean
--   theorem TropicalLA.IsTropEigen.exists_critical_cycle(h : IsTropEigen A lam v) :
--       ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
--         Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) ∧
--         (∀ i, A i (f i) + v (f i) = lam + v i) ∧
--         pathWeight A (fun t => f^[t] y) p = p * lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalEigenvalue.lean#L131

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

theorem TropicalLA.IsTropEigen.exists_critical_cycle(h : IsTropEigen A lam v) :
    ∃ (f : ι → ι) (y : ι) (p : ℕ), 0 < p ∧ f^[p] y = y ∧
      Set.InjOn (fun t => f^[t] y) (Finset.range p : Finset ℕ) ∧
      (∀ i, A i (f i) + v (f i) = lam + v i) ∧
      pathWeight A (fun t => f^[t] y) p = p * lam := by sorry
