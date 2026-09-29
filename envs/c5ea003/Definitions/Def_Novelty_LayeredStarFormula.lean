-- Prove2me | Definitions.Def_Novelty_LayeredStarFormula
-- name    : Novelty_LayeredStarFormula
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:03.409542+00:00
-- url     : https://prove2.me/theorems/c0631401-6fe3-4f5a-9f4e-d4849f19e007
-- title:
--   Aether Catalog definitions — Novelty_LayeredStarFormula
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.LayeredStarFormula`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/LayeredStarFormula.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The layered-star formula `Mformula` and its central-layer maximum

This file develops the counting machinery behind the *uniform layered-star*
VC-dimension construction (see `UniformVCStar.lean`).

* `layeredSum n d = ∑_{k=0}^{d} C(n,k)` is the Sauer–Shelah growth bound; we prove
  it is **monotone** in both the layer budget `d` (`layeredSum_mono_d`) and the
  number of points `n` (`layeredSum_mono_n`), and bounded above by `2 ^ n`.
* `starLayer d k = C(d,k)` is the size profile of star layer `k`; it attains its
  **maximum at `k = ⌊d/2⌋`** (`starLayer_max`), the middle binomial coefficient.
* `Mformula n d = C(n, ⌊d/2⌋)` is the size of the central uniform layer, a single
  summand of `layeredSum` (`Mformula_le_layeredSum`).

These statements correspond, via `import Mathlib`, to `Nat.choose_le_middle`,
`Nat.choose_mono`, and `Nat.sum_range_choose`; the companion thin wrappers live in
`Binomial.lean`.
-/

open Finset

namespace Catalog.Novelty.LayeredStar

/-- `layeredSum n d = ∑_{k=0}^{d} C(n,k)`, the Sauer–Shelah growth bound. -/
def layeredSum (n d : ℕ) : ℕ := ∑ k ∈ Finset.range (d + 1), n.choose k





/-- The number of sets contributed by star layer `k` in a depth-`d` construction. -/
def starLayer (d k : ℕ) : ℕ := d.choose k


/-- `Mformula n d = C(n, ⌊d/2⌋)`, the size of the central uniform layer. -/
def Mformula (n d : ℕ) : ℕ := n.choose (d / 2)




end Catalog.Novelty.LayeredStar


