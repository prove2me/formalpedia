-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyTotalVariation
-- name    : Novelty_UniversalRedundancyTotalVariation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:49:24.969978+00:00
-- url     : https://prove2.me/theorems/4776c174-9259-44dd-9e6a-7cc4d313cbe7
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyTotalVariation
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyTotalVariation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyTotalVariation.lean by skeleton subtraction
import Mathlib
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

namespace PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]

/-- Total variation distance between the two members of a two-element class. -/
noncomputable def tv (p : Fin 2 → A → ℝ) : ℝ := (1/2) * ∑ a, |p 0 a - p 1 a|








end PriceOfUniversality


