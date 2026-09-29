-- Prove2me | Theorems.Thm_AffineStats_flatProb_codimSub_prod
-- name    : AffineStats.flatProb_codimSub_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:18:18.776722+00:00
-- url     : https://prove2.me/theorems/0ebd18d5-e108-4a82-a87f-5d555626d733
-- title:
--   The exact probability.
-- statement:
--   **The exact probability.** For `m ≤ n` and `m ≤ d`, a uniformly random affine `d`-cube
--   meets the codimension-`m` coordinate subspace of `𝔽₂ⁿ` in exactly `2^{d-m}` points with
--   probability exactly `∏_{i<m}(1 - 2^{i-d})`.  Note that the value does not depend on `n`.
--
--   ```lean
--   theorem AffineStats.flatProb_codimSub_prod(hmn : m ≤ n) (hmd : m ≤ d) :
--       flatProb n d (codimSub n hmn) (2 ^ (d - m))
--         = ∏ i : Fin m, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AffineSubspaceStats/ExactProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AffineSubspaceStats/ExactProduct.lean#L166

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

theorem AffineStats.flatProb_codimSub_prod(hmn : m ≤ n) (hmd : m ≤ d) :
    flatProb n d (codimSub n hmn) (2 ^ (d - m))
      = ∏ i : Fin m, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ d) := by sorry
