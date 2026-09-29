-- Prove2me | Theorems.Thm_StereographicCapacity_card_lt_of_inner_lt_simplex_threshold
-- name    : StereographicCapacity.card_lt_of_inner_lt_simplex_threshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:22:22.532501+00:00
-- url     : https://prove2.me/theorems/578b259c-620c-49b2-839f-112461bdf4d6
-- title:
--   If every distinct pair of unit vectors has inner product strictly below the
-- statement:
--   If every distinct pair of unit vectors has inner product strictly below the
--   simplex threshold, then the family has fewer than `N` elements.
--
--   ```lean
--   theorem StereographicCapacity.card_lt_of_inner_lt_simplex_threshold    {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       (s : Finset ι) (v : ι → E) (N : ℕ)
--       (hN : 2 ≤ N)
--       (hunit : ∀ i ∈ s, ‖v i‖ = 1)
--       (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
--         inner ℝ (v i) (v j) < -(1 / ((N : ℝ) - 1))) :
--       s.card < N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/StereographicCapacity/SimplexBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/StereographicCapacity/SimplexBound.lean#L84

-- Thm stub generated from Geometry/StereographicCapacity/SimplexBound.lean
import Mathlib

/-!
# The simplex bound for spherical codes

This file proves the dimension-free simplex bound.  If a finite family of unit
vectors has every distinct pairwise inner product at most `c`, then
`c ≥ -1/(N-1)`, where `N` is the number of vectors.  The result follows from
positivity of the Gram matrix, applied to the all-ones vector.
-/

-- open removed: section is not a namespace

theorem StereographicCapacity.card_lt_of_inner_lt_simplex_threshold    {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Finset ι) (v : ι → E) (N : ℕ)
    (hN : 2 ≤ N)
    (hunit : ∀ i ∈ s, ‖v i‖ = 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      inner ℝ (v i) (v j) < -(1 / ((N : ℝ) - 1))) :
    s.card < N := by sorry
