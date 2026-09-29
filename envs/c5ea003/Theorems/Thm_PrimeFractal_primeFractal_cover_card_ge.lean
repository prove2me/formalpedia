-- Prove2me | Theorems.Thm_PrimeFractal_primeFractal_cover_card_ge
-- name    : PrimeFractal.primeFractal_cover_card_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:33:23.280009+00:00
-- url     : https://prove2.me/theorems/e7881cc3-7610-4ae9-a5fa-bcb613c3c055
-- title:
--   Covering form of the lower bound.
-- statement:
--   **Covering form of the lower bound.**  For every `ε > 0`, eventually in `m`: any
--   finite family of intervals of length `1/m` covering the prime fractal has at least
--   `m ^ (1 - ε)` members.  The box dimension `1` is therefore not an artefact of the grid.
--
--   ```lean
--   theorem PrimeFractal.primeFractal_cover_card_ge{ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ m : ℕ in atTop, ∀ I : Set ℝ, I.Finite →
--         primeFractal ⊆ (⋃ c ∈ I, Set.Icc c (c + 1 / (m : ℝ))) →
--         1 - ε ≤ Real.log I.ncard / Real.log m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalCovering.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalCovering.lean#L65

-- Thm stub generated from NumberTheory/PrimeFractalCovering.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Definitions.Def_NumberTheory_PrimeFractalRefined

/-!
# Robustness of the box dimension: grid boxes versus arbitrary covers

`NumberTheory.PrimeFractalBoxDimension` computes the box dimension of the prime
fractal with *grid* boxes `[k/m, (k+1)/m)`.  A critic may object that the value
of a "dimension" must not depend on that choice.  It does not: an interval of
length `1/m` meets at most two grid boxes, so any cover of `S` by `K` intervals
of length `1/m` satisfies `boxCountSet S m ≤ 2 K`.

Consequently the dimension-`1` lower bound survives verbatim for the
covering-number definition of the Minkowski dimension
(`primeFractal_cover_card_ge`): however cleverly one covers the primes by
intervals of length `1/m`, one needs `m^{1-o(1)}` of them.
-/

open PrimeFractal

open Filter Topology

theorem PrimeFractal.primeFractal_cover_card_ge{ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ I : Set ℝ, I.Finite →
      primeFractal ⊆ (⋃ c ∈ I, Set.Icc c (c + 1 / (m : ℝ))) →
      1 - ε ≤ Real.log I.ncard / Real.log m := by sorry
