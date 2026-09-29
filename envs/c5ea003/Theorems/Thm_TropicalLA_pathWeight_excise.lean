-- Prove2me | Theorems.Thm_TropicalLA_pathWeight_excise
-- name    : TropicalLA.pathWeight_excise
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:19:31.624906+00:00
-- url     : https://prove2.me/theorems/0294f472-f3ea-4253-a519-e91d8accc681
-- title:
--   Walk excision.
-- statement:
--   **Walk excision.**  If a walk `p` of length `m` visits the same vertex at times
--   `a < b`, then deleting the closed sub-walk between those times leaves a walk with the
--   same endpoints, and the two weights add up to the original weight.
--
--   ```lean
--   theorem TropicalLA.pathWeight_excise(A : Matrix ι ι ℝ) (p : ℕ → ι) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m)
--       (hp : p a = p b) :
--       pathWeight A (fun t => if t < a then p t else p (t + (b - a))) (m - (b - a))
--         + pathWeight A (fun t => p (a + t)) (b - a) = pathWeight A p m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalPerronFrobenius.lean#L32

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


omit [Fintype ι] [Nonempty ι] in

theorem TropicalLA.pathWeight_excise(A : Matrix ι ι ℝ) (p : ℕ → ι) {a b m : ℕ} (hab : a < b) (hbm : b ≤ m)
    (hp : p a = p b) :
    pathWeight A (fun t => if t < a then p t else p (t + (b - a))) (m - (b - a))
      + pathWeight A (fun t => p (a + t)) (b - a) = pathWeight A p m := by sorry
