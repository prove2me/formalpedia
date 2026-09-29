-- Prove2me | Theorems.Thm_TropicalLA_exists_critical_cycle_maxCycleMean
-- name    : TropicalLA.exists_critical_cycle_maxCycleMean
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:33:28.564397+00:00
-- url     : https://prove2.me/theorems/c1b6c1ad-f8da-4b49-b13e-19b10fdbdd48
-- title:
--   The maximum cycle mean is attained: there is a critical cycle of length
-- statement:
--   The maximum cycle mean is attained: there is a **critical cycle** of length
--   `1 ≤ m ≤ n` whose mean weight equals `maxCycleMean A`.
--
--   ```lean
--   theorem TropicalLA.exists_critical_cycle_maxCycleMean:
--       ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ m ≤ Fintype.card ι ∧ c m = c 0 ∧
--         pathWeight A c m = m * maxCycleMean A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean#L193

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# Tropical Perron–Frobenius: existence of the eigenvalue

This file completes the max-plus spectral theory of `TropicalEigenvalue.lean` by
proving **existence**: every matrix with finite real entries has a tropical
eigenvalue, namely its maximum cycle mean, together with an explicit eigenvector
built from the Kleene star (optimal-path) matrix of the normalised matrix.

The combinatorial engine is `pathWeight_excise`: a walk that repeats a vertex
splits into a shorter walk with the same endpoints plus a closed sub-walk.
Together with the pigeonhole principle this yields

* `cycle_le_maxCycleMean` : *every* closed walk, of any length, has weight at most
  `length · λ` where `λ` is the maximum mean over closed walks of length `≤ n`;
* `exists_short_walk_ge`  : when all cycles are nonpositive, every walk is dominated
  by one of length at most `n` with the same endpoints;
* `exists_tropEigen`      : **tropical Perron–Frobenius** — `A` has the eigenvalue
  `maxCycleMean A`, with an eigenvector given by optimal paths into a critical node.

Combined with `tropEigenvalue_unique` this says: a max-plus matrix with finite
entries has *exactly one* eigenvalue, the maximum cycle mean.
-/

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]






variable (A : Matrix ι ι ℝ)



variable {A}

theorem TropicalLA.exists_critical_cycle_maxCycleMean:
    ∃ (m : ℕ) (c : ℕ → ι), 0 < m ∧ m ≤ Fintype.card ι ∧ c m = c 0 ∧
      pathWeight A c m = m * maxCycleMean A := by sorry
