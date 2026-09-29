-- Prove2me | Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
-- name    : Applications_AffineSubspaceStats_RandomConstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:31:58.657374+00:00
-- url     : https://prove2.me/theorems/453e7be3-f3d8-4dcc-a6c0-00f1d2dfd0d3
-- title:
--   Aether Catalog definitions — Applications_AffineSubspaceStats_RandomConstruction
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.AffineSubspaceStats.RandomConstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/AffineSubspaceStats/RandomConstruction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
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

namespace AffineStats

open Finset

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]




end Counting

section RandomSet

variable {n d : ℕ}

/-- The subset of `𝔽₂ⁿ` cut out by a colouring: the fibre over `0`. -/
def colSet (m : ℕ) (g : Vec n → Fin (m + 1)) : Finset (Vec n) :=
  univ.filter fun x => g x = 0

/-- The point set of the affine cube with parameters `(c, v)`. -/
def cubeSet (c : Vec n) (v : Fin d → Vec n) : Finset (Vec n) :=
  univ.image (pt c v)




end RandomSet

section Averaging



end Averaging

section MainBound





end MainBound

section Comparison


end Comparison

section Asymptotics

open Filter



end Asymptotics

end AffineStats


