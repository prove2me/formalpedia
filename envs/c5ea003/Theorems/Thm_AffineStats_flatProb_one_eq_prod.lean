-- Prove2me | Theorems.Thm_AffineStats_flatProb_one_eq_prod
-- name    : AffineStats.flatProb_one_eq_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:19:00.870326+00:00
-- url     : https://prove2.me/theorems/a0b871d3-58ea-442a-930e-15566eca8e8c
-- title:
--   The case `s = 1`.
-- statement:
--   **The case `s = 1`.** Taking the codimension-`d` subspace of `𝔽₂ⁿ` (`d ≤ n`), a random
--   affine `d`-cube meets it in exactly one point with probability `∏_{i<d}(1 - 2^{i-d})`.  This
--   gives the lower bound `λ*(d, 1) ≥ ∏_{i<d}(1 - 2^{i-d})`, which equals `1/2` for `d = 1` and
--   decreases to `∏_{t≥1}(1 - 2^{-t}) ≈ 0.2887…` as `d → ∞`.
--
--   ```lean
--   theorem AffineStats.flatProb_one_eq_prod(hdn : d ≤ n) :
--       flatProb n d (codimSub n hdn) 1 = ∏ i : Fin d, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AffineSubspaceStats/ExactProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AffineSubspaceStats/ExactProduct.lean#L203

-- Thm stub generated from Applications/AffineSubspaceStats/ExactProduct.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the exact value of the codimension-`m` construction

This file completes the analysis of the codimension-`m` lower-bound construction begun in
`Catalog/Applications/AffineSubspaceStats/CodimSubspace.lean`.  There it was shown that a
random affine `d`-cube meets the codimension-`m` subspace `A ⊆ 𝔽₂ⁿ` in exactly `2^{d-m}`
points *iff* the projected directions span `𝔽₂^m` (for `m ≤ d`), and that this happens with
probability at least `1 - (2^m - 1)/2^d`.

Here we compute the probability exactly:

`P[|F ∩ A| = 2^{d-m}] = ∏_{i<m} (1 - 2^{i-d})`,

for all `n ≥ m` and `d ≥ m`.  With `k = d - m` the right-hand side is
`∏_{t=k+1}^{d} (1 - 2^{-t})`, the exact value of the classical lower-bound construction for
the affine subspace statistics problem; in particular it is `≥ 1 - 2^{-k}` and tends to
`1 - 2^{-k}` from above only up to the explicit correction computed here.

The proof has three ingredients:

* the fibers of the coordinate projection `π : 𝔽₂ⁿ → 𝔽₂^m` all have the same size, so the
  count of good direction tuples in `𝔽₂ⁿ` reduces to the count of good tuples in `𝔽₂^m`
  (`card_surj_dirs`);
* `y ↦ ∑ yᵢwᵢ` is surjective iff the transposed family of `m` vectors of `𝔽₂^d` is linearly
  independent (`surj_iff_linearIndependent`);
* the number of linearly independent `m`-tuples in `𝔽₂^d` is `∏_{i<m}(2^d - 2^i)`
  (Mathlib's `card_linearIndependent`).
-/

open AffineStats

open Finset


variable {n m d : ℕ}

theorem AffineStats.flatProb_one_eq_prod(hdn : d ≤ n) :
    flatProb n d (codimSub n hdn) 1 = ∏ i : Fin d, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) := by sorry
