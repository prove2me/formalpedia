-- Prove2me | Theorems.Thm_AffineStats_card_surj_dirs
-- name    : AffineStats.card_surj_dirs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:17:05.367714+00:00
-- url     : https://prove2.me/theorems/31f6e33e-ed79-4dce-b6e2-86a21db4f494
-- title:
--   Counting good direction tuples in `𝔽₂ⁿ` reduces to counting them in `𝔽₂^m`.
-- statement:
--   Counting good direction tuples in `𝔽₂ⁿ` reduces to counting them in `𝔽₂^m`.
--
--   ```lean
--   theorem AffineStats.card_surj_dirs(hmn : m ≤ n) (d : ℕ) :
--       2 ^ (m * d) *
--           (univ.filter fun v : Fin d → Vec n =>
--             Function.Surjective (Lmap fun i => proj hmn (v i))).card
--         = (univ.filter fun w : Fin d → Vec m =>
--             Function.Surjective (Lmap w)).card * 2 ^ (n * d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AffineSubspaceStats/ExactProduct.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AffineSubspaceStats/ExactProduct.lean#L82

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

theorem AffineStats.card_surj_dirs(hmn : m ≤ n) (d : ℕ) :
    2 ^ (m * d) *
        (univ.filter fun v : Fin d → Vec n =>
          Function.Surjective (Lmap fun i => proj hmn (v i))).card
      = (univ.filter fun w : Fin d → Vec m =>
          Function.Surjective (Lmap w)).card * 2 ^ (n * d) := by sorry
