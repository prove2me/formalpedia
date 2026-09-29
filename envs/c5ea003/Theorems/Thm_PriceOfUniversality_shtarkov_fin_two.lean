-- Prove2me | Theorems.Thm_PriceOfUniversality_shtarkov_fin_two
-- name    : PriceOfUniversality.shtarkov_fin_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:26:19.314892+00:00
-- url     : https://prove2.me/theorems/72099527-3dfc-4cbf-854b-6c9bb3ab2d1c
-- title:
--   Closed form for the Shtarkov sum of a two-source class.
-- statement:
--   **Closed form for the Shtarkov sum of a two-source class.**
--
--   ```lean
--   theorem PriceOfUniversality.shtarkov_fin_two{p : Fin 2 → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
--       shtarkov p = 1 + tv p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyTotalVariation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyTotalVariation.lean#L39

-- Thm stub generated from Novelty/UniversalRedundancyTotalVariation.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Definitions.Def_Novelty_UniversalRedundancyTotalVariation
/-
# The price of universality, X: an exact closed form for two sources

The rigidity theorem of `UniversalRedundancyRigidity.lean` says the price of
universality measures distinguishability rather than cardinality.  For a class of
**two** sources we can say exactly how:

  `S({p₀, p₁}) = 1 + TV(p₀, p₁)`,

`TV` the total variation distance, so the exact minimax regret is

  `log₂ (1 + TV(p₀, p₁))`  bits,

interpolating continuously between `0` bits for identical sources and `1` bit —
the cost of naming the source — for perfectly distinguishable ones.  This is the
first *closed form* in the programme: the price of universality of a two-element
class is a metric quantity.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]

theorem PriceOfUniversality.shtarkov_fin_two{p : Fin 2 → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) :
    shtarkov p = 1 + tv p := by sorry
