-- Prove2me | Theorems.Thm_PriceOfUniversality_kl_nml_le_logb_shtarkov
-- name    : PriceOfUniversality.kl_nml_le_logb_shtarkov
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:24:45.427506+00:00
-- url     : https://prove2.me/theorems/c3c0f277-9c62-42a0-93c0-9995751b43e4
-- title:
--   Every member of the class is within `log₂ S` bits of NML *on average*, not just
-- statement:
--   Every member of the class is within `log₂ S` bits of NML *on average*, not just
--   pointwise.
--
--   ```lean
--   theorem PriceOfUniversality.kl_nml_le_logb_shtarkov{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
--       (hpos : ∀ a, 0 < maxLik p a) (θ : Θ) :
--       kl (p θ) (nml p) ≤ logb 2 (shtarkov p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancySharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancySharpness.lean#L37

-- Thm stub generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
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

omit [Nonempty A] in

theorem PriceOfUniversality.kl_nml_le_logb_shtarkov{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (hpos : ∀ a, 0 < maxLik p a) (θ : Θ) :
    kl (p θ) (nml p) ≤ logb 2 (shtarkov p) := by sorry
