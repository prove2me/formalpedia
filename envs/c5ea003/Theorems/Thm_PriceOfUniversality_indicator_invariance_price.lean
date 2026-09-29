-- Prove2me | Theorems.Thm_PriceOfUniversality_indicator_invariance_price
-- name    : PriceOfUniversality.indicator_invariance_price
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:24:04.369455+00:00
-- url     : https://prove2.me/theorems/f8f8b700-4d57-43af-806a-56096e1bf9ae
-- title:
--   The invariance price is attained.
-- statement:
--   **The invariance price is attained.**  Specialising the class of `m`
--   deterministic sources to a single one of them saves exactly `log₂ m` bits on the
--   message that source emits: the whole cost of naming the source, and nothing
--   more.
--
--   ```lean
--   theorem PriceOfUniversality.indicator_invariance_price[NeZero m] :
--       logb 2 (nml (indicatorSub m) (0 : Fin m)) - logb 2 (nml (indicatorClass m) (0 : Fin m))
--         = logb 2 m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyInvariance.lean#L136

-- Thm stub generated from Novelty/UniversalRedundancyInvariance.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyInvariance
import Definitions.Def_Novelty_UniversalRedundancySharpness
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
/-
# The price of universality, VIII: an invariance theorem with an explicit price

Algorithmic information theory's invariance theorem says that two universal
machines differ by an additive constant, but the constant is opaque.  In the
statistical setting the constant is *computable*: if `P' ⊆ P` are classes of
sources and `U'`, `U` are their normalised maximum likelihood codes, then on
every message the specialised code `U'` beats the more general code `U` by at
most

  `log₂ S(P) − log₂ S(P')`  bits,

i.e. exactly the ratio of the two Shtarkov normalisers, and this is **attained**
on any message whose maximum likelihood is achieved inside the subclass
(`nml_excess_eq`).  A concrete witness — the `m` deterministic sources with the
one-element subclass — realises the full `log₂ m` bits
(`indicator_invariance_price`), so the bound is not vacuous.

Reading this back into the research programme: **the entire benefit of a
specialised decompressor is the logarithm of how much model class it throws
away.**  Nothing else about the specialisation matters.
-/

open PriceOfUniversality

open Finset Real


variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ Θ' : Type*} [Fintype Θ] [Nonempty Θ] [Fintype Θ'] [Nonempty Θ']








/-! ## A one-source subclass, and the exact value of specialising -/


variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]




variable {m : ℕ}

theorem PriceOfUniversality.indicator_invariance_price[NeZero m] :
    logb 2 (nml (indicatorSub m) (0 : Fin m)) - logb 2 (nml (indicatorClass m) (0 : Fin m))
      = logb 2 m := by sorry
