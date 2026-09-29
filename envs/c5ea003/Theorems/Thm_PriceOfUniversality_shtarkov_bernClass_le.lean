-- Prove2me | Theorems.Thm_PriceOfUniversality_shtarkov_bernClass_le
-- name    : PriceOfUniversality.shtarkov_bernClass_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:25:58.299984+00:00
-- url     : https://prove2.me/theorems/046c3b28-2896-4644-89bd-b803668b8ba0
-- title:
--   Upper bound on the Shtarkov sum of the memoryless binary class.
-- statement:
--   **Upper bound on the Shtarkov sum of the memoryless binary class.**
--
--   ```lean
--   theorem PriceOfUniversality.shtarkov_bernClass_le(n : ℕ) : shtarkov (bernClass n) ≤ (n : ℝ) + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancySharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancySharpness.lean#L222

-- Thm stub generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
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

open PriceOfUniversality

open Finset Real

/-! ## Bridge: the average-case price never exceeds the worst-case price -/


variable {A : Type*} [Fintype A] [Nonempty A] {Θ : Type*} [Fintype Θ] [Nonempty Θ]




/-! ## A concrete class realising the exact price `log₂ m` -/


variable {m : ℕ}









/-! ## The Bernoulli class: matching upper bound of order `log n` -/

theorem PriceOfUniversality.shtarkov_bernClass_le(n : ℕ) : shtarkov (bernClass n) ≤ (n : ℝ) + 1 := by sorry
