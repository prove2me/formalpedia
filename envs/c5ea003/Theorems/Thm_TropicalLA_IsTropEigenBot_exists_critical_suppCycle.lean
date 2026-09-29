-- Prove2me | Theorems.Thm_TropicalLA_IsTropEigenBot_exists_critical_suppCycle
-- name    : TropicalLA.IsTropEigenBot.exists_critical_suppCycle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:13:53.997909+00:00
-- url     : https://prove2.me/theorems/47a4228d-da47-4f6b-b548-2ccc2d739341
-- title:
--   A critical support cycle exists: following the tight successors must close up.
-- statement:
--   A **critical support cycle** exists: following the tight successors must close up.
--
--   ```lean
--   theorem TropicalLA.IsTropEigenBot.exists_critical_suppCycle(h : IsTropEigenBot A lam v) :
--       ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ c m = c 0 ∧ IsSuppWalk A c m ∧
--         pathWeight (finPart A) c m = m * lam := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalIrreducible.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalIrreducible.lean#L438

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalIrreducible.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# Tropical Perron–Frobenius with `−∞` entries

This file settles conjecture **C4** of `FUTURE_DIRECTIONS.md`.  Matrices are now
allowed genuine tropical zeros `⊥ = −∞`, i.e. `A : Matrix ι ι (WithBot ℝ)`, and an
*eigenvector* is still required to be **finite** (`v : ι → ℝ`):

  `IsTropEigenBot A lam v : ∀ i, ⨆ j (A i j + v j) = lam + v i`   (sup in `WithBot ℝ`).

Main results:

* `exists_tropEigenBot_of_stronglyConnected` — **existence**: if the support digraph
  `Supp A` (the pairs with `A i j ≠ ⊥`) is strongly connected, then `A` has a tropical
  eigenvalue with a finite eigenvector.  The proof is a *perturbation* argument: replace
  every `⊥` by a finite but very negative penalty, apply the finite-entry
  Perron–Frobenius theorem `exists_tropEigen`, normalise the eigenvector to have maximum
  `0`, and show — using short support walks — that its entries stay in a fixed compact
  interval that does not depend on the penalty.  Hence for a large enough penalty no
  optimal row entry can use a `⊥` position, and the eigenvector of the perturbed matrix
  is an eigenvector of `A` itself.
* `IsTropEigenBot.isGreatest_suppCycleMean` — the eigenvalue is exactly the maximum mean
  weight of a closed walk in the support digraph, and hence
* `tropEigenvalueBot_unique` — **uniqueness** of the eigenvalue, *without* any
  irreducibility hypothesis.
* `not_stronglyConnected_of_isTropEigenBot_false` — the converse half of C4 is **false**:
  the `2 × 2` matrix `diag(0, 0)` (with `⊥` off the diagonal) has the finite eigenvector
  `(0,0)` although its support digraph is not strongly connected.  So strong connectivity
  is sufficient but not necessary, and C4 must be weakened to the implication proved here.

Auxiliary combinatorics, of independent interest:

* `exists_short_supp_walk` — in a strongly connected digraph on `n` vertices any two
  vertices are joined by a walk of length between `1` and `n` (proved by excising
  repeated vertices);
* `IsTropEigen.pathWeight_le` — the telescoping bound `w(p) + v(p m) ≤ m·lam + v(p 0)`
  for a finite-entry eigenpair, which generalises `IsTropEigen.cycle_le`.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Matrices over `WithBot ℝ`: support, walks, eigenpairs -/


variable (A : Matrix ι ι (WithBot ℝ))








variable {A : Matrix ι ι (WithBot ℝ)}



open IsTropEigenBot

variable {lam : ℝ} {v : ι → ℝ}





/-! ## Short walks in a strongly connected support digraph -/




/-! ## Telescoping along a walk, for finite-entry eigenpairs -/



/-! ## The perturbed matrix -/


variable (A)






variable {A}















/-! ## Existence of an eigenvector with `⊥` entries -/


/-! ## The eigenvalue is the maximum support cycle mean -/

open IsTropEigenBot

variable {lam : ℝ} {v : ι → ℝ}

theorem TropicalLA.IsTropEigenBot.exists_critical_suppCycle(h : IsTropEigenBot A lam v) :
    ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ c m = c 0 ∧ IsSuppWalk A c m ∧
      pathWeight (finPart A) c m = m * lam := by sorry
