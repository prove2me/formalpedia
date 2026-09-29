-- Prove2me | Theorems.Thm_PriceOfUniversality_price_unbounded_in_parameters
-- name    : PriceOfUniversality.price_unbounded_in_parameters
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:25:44.151735+00:00
-- url     : https://prove2.me/theorems/de471f9d-8597-4d5a-b70f-c60c1aeb3eff
-- title:
--   The price of universality is unbounded in the number of parameters.
-- statement:
--   **The price of universality is unbounded in the number of parameters.**
--   For any target `C` and any block length `n ≥ 32` there is a number of independent
--   components `k` for which every code pays more than `C` bits of regret.
--
--   ```lean
--   theorem PriceOfUniversality.price_unbounded_in_parameters(C : ℝ) (n : ℕ) (hn : 32 ≤ n) :
--       ∃ k : ℕ, ∀ {L : (Fin k → Msg n) → ℕ}, IsCode L →
--         ∃ (j : Fin k → Fin (n + 1)) (x : Fin k → Msg n),
--           C ≤ (L x : ℝ) + Real.logb 2 (kBernClass k n j x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyPi.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyPi.lean#L142

-- Thm stub generated from Novelty/UniversalRedundancyPi.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyPi
import Definitions.Def_Novelty_UniversalRedundancyProduct
import Definitions.Def_Novelty_UniversalRedundancySharpness
/-
# The price of universality, VII: the full `k`-parameter Rissanen rate

`UniversalRedundancyProduct.lean` proved that the Shtarkov sum is multiplicative
over a product of *two* independent classes.  Here we upgrade this to an
arbitrary finite family of independent components,

  `S(⨂ i, P i) = ∏ i, S(P i)`,  hence  `regret(⨂ i, P i) = ∑ i, regret(P i)`,

and combine it with the `√n` lower bound for the memoryless binary class to
obtain the genuine **`k`-parameter Rissanen rate**: every code for `k`
independent binary blocks of length `n` must pay, on some message and against
some member of the class,

  `k · ((1/2) log₂ n − 2)`  bits of regret,

while the normalised maximum likelihood code pays at most
`k · log₂ (n + 1)` bits.  So the price of universality for a `k`-parameter
memoryless model is `Θ(k log n)`: *linear in the number of free parameters,
logarithmic in the block length.*

The research verdict this file supports: a decompressor specialised to one
component of the model class buys back exactly the regret of that component and
nothing more, and those savings add up over independent components.
-/

open PriceOfUniversality

open Finset Real


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)]
variable {Θ : ι → Type*} [∀ i, Fintype (Θ i)] [∀ i, Nonempty (Θ i)]








/-! ## The `k`-parameter Rissanen rate for memoryless binary blocks -/

theorem PriceOfUniversality.price_unbounded_in_parameters(C : ℝ) (n : ℕ) (hn : 32 ≤ n) :
    ∃ k : ℕ, ∀ {L : (Fin k → Msg n) → ℕ}, IsCode L →
      ∃ (j : Fin k → Fin (n + 1)) (x : Fin k → Msg n),
        C ≤ (L x : ℝ) + Real.logb 2 (kBernClass k n j x) := by sorry
