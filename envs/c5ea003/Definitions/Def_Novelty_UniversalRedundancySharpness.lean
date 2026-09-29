-- Prove2me | Definitions.Def_Novelty_UniversalRedundancySharpness
-- name    : Novelty_UniversalRedundancySharpness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:48:51.370224+00:00
-- url     : https://prove2.me/theorems/560784a2-cb53-4701-9c8e-c5f1a2f622e6
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancySharpness
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancySharpness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancySharpness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyProduct
/-
# The price of universality, VI: sharpness, non-vacuity and the two-sided rate

Adversarial review of the preceding files.  Two questions are settled here.

**1. Are the hypotheses of the "exact price" theorems satisfiable?**
`indicatorClass_sandwich` exhibits a concrete class — the `m` deterministic
sources on an alphabet of size `m` — that satisfies every hypothesis of
`price_of_universality_sandwich` and `minimax_regret_disjoint`, so those results
are not vacuous.  For this class the general theory specialises to a sharp
pigeonhole statement about code lengths, `exists_length_ge_logb_card`: any Kraft
code on `m` messages assigns some message a length of at least `log₂ m`.

**2. Is the `(1/2) log₂ n` lower bound of the Bernoulli class of the right
order?**  `shtarkov_bernClass_le` shows `S ≤ n + 1`, hence the exact minimax
regret of the memoryless binary class of block length `n` obeys

  `(1/2) log₂ n − 2  ≤  regret  ≤  log₂ (n + 1)`.

So the truth is pinned between `(1/2) log₂ n` and `log₂ n`; the classical
`(1/2) log₂ n + O(1)` answer sits at the lower end, and no bound better than
linear in `log n` is possible.  Closing the factor-of-two gap requires the
Stirling-type estimate discussed in `FUTURE_DIRECTIONS.md`.
-/

namespace PriceOfUniversality

open Finset Real

/-! ## Bridge: the average-case price never exceeds the worst-case price -/

section Bridge

variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]



end Bridge

/-! ## A concrete class realising the exact price `log₂ m` -/

/-- The class of `m` deterministic sources on an alphabet of `m` letters: source
`θ` emits the letter `θ` with certainty.  These are perfectly distinguishable. -/
noncomputable def indicatorClass (m : ℕ) : Fin m → Fin m → ℝ :=
  fun θ a => if a = θ then 1 else 0

variable {m : ℕ}









/-! ## The Bernoulli class: matching upper bound of order `log n` -/





end PriceOfUniversality


