-- Prove2me | Theorems.Thm_PriceOfUniversality_mutualInfo_le_logb_shtarkov
-- name    : PriceOfUniversality.mutualInfo_le_logb_shtarkov
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:25:03.788036+00:00
-- url     : https://prove2.me/theorems/49ba89aa-a70f-429d-8fa3-ef7ee8800e8a
-- title:
--   The average-case price of universality never exceeds the worst-case price.
-- statement:
--   **The average-case price of universality never exceeds the worst-case price.**
--   For every prior on the class, the mutual information (the average-case price of
--   `exists_source_redundancy_ge_mutualInfo`) is at most `log₂ S` (the exact
--   worst-case price of `minimax_regret_eq_logb_shtarkov`).
--
--   ```lean
--   theorem PriceOfUniversality.mutualInfo_le_logb_shtarkov{pri : Θ → ℝ} {p : Θ → A → ℝ}
--       (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
--       (hpos : ∀ a, 0 < maxLik p a) :
--       mutualInfo pri p ≤ logb 2 (shtarkov p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancySharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancySharpness.lean#L60

-- Thm stub generated from Novelty/UniversalRedundancySharpness.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
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

theorem PriceOfUniversality.mutualInfo_le_logb_shtarkov{pri : Θ → ℝ} {p : Θ → A → ℝ}
    (hpri : IsPMF pri) (hpripos : ∀ θ, 0 < pri θ) (hp : ∀ θ, IsPMF (p θ))
    (hpos : ∀ a, 0 < maxLik p a) :
    mutualInfo pri p ≤ logb 2 (shtarkov p) := by sorry
