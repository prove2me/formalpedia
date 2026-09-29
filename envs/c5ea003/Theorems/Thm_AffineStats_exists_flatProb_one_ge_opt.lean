-- Prove2me | Theorems.Thm_AffineStats_exists_flatProb_one_ge_opt
-- name    : AffineStats.exists_flatProb_one_ge_opt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:17:52.417185+00:00
-- url     : https://prove2.me/theorems/c89c6cf9-cc08-4503-9243-adaf82eef3be
-- title:
--   The optimal choice `p = 2^{-(d+1)}`.
-- statement:
--   **The optimal choice `p = 2^{-(d+1)}`.** Taking `m + 1 = 2^{d+1}` gives
--   `λ(d+1, 1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1}·(1 - (2^{d+1}-1)/2ⁿ)`.
--
--   ```lean
--   theorem AffineStats.exists_flatProb_one_ge_opt(n d : ℕ) (hdn : d + 1 ≤ n) :
--       ∃ A : Finset (Vec n),
--         (((2 : ℚ) ^ (d + 1) - 1) / 2 ^ (d + 1)) ^ (2 ^ (d + 1) - 1)
--             * (1 - (2 ^ (d + 1) - 1) / 2 ^ n) ≤ flatProb n (d + 1) A 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AffineSubspaceStats/RandomConstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AffineSubspaceStats/RandomConstruction.lean#L350

-- Thm stub generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the random construction for `s = 1`

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up.

The paper's `s = 1` regime is governed by a *random* construction: keep each point of
`𝔽₂ⁿ` independently with probability `p`.  A `d`-flat `F` has `2^d` points, so it meets
such a random set in exactly one point with probability `2^d · p · (1-p)^{2^d - 1}`,
which is maximised at `p = 2^{-d}`, giving `(1 - 2^{-d})^{2^d - 1} → e^{-1}`.

We formalise this as a *counting* argument (no measure theory): instead of a random
subset we average over the `(m+1)^{2ⁿ}` colourings `g : 𝔽₂ⁿ → Fin (m+1)` and take
`A = g⁻¹(0)`, which realises `p = 1/(m+1)` exactly.  The combinatorial heart is
`AffineStats.card_exactly_one`: for a fixed set `T` of `t` points, exactly
`t · m^{t-1} · (m+1)^{|α| - t}` colourings vanish at exactly one point of `T`.

The main results are

* `AffineStats.exists_flatProb_one_ge` :
  `∃ A, λ(d+1,1) ≥ (2^{d+1}·m^{2^{d+1}-1} / (m+1)^{2^{d+1}}) · (1 - (2^{d+1}-1)/2ⁿ)`
  for every `m`;
* `AffineStats.exists_flatProb_one_ge_opt` : the choice `m + 1 = 2^{d+1}`, giving
  `λ(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1} · (1 - (2^{d+1}-1)/2ⁿ)`;
* `AffineStats.maxFlatProb_one_ge_limit` : hence
  `λ*(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1}`, which for `d = 0` is the exact value `1/2`
  and for every `d` beats the algebraic construction of
  `Catalog/Applications/AffineSubspaceStats/ExactProduct.lean` (e.g. `27/64` versus
  `3/8` for `2`-flats).
-/

open AffineStats

open Finset


variable {α : Type*} [Fintype α] [DecidableEq α]






variable {n d : ℕ}

theorem AffineStats.exists_flatProb_one_ge_opt(n d : ℕ) (hdn : d + 1 ≤ n) :
    ∃ A : Finset (Vec n),
      (((2 : ℚ) ^ (d + 1) - 1) / 2 ^ (d + 1)) ^ (2 ^ (d + 1) - 1)
          * (1 - (2 ^ (d + 1) - 1) / 2 ^ n) ≤ flatProb n (d + 1) A 1 := by sorry
