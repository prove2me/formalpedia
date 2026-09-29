-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyInvariance
-- name    : Novelty_UniversalRedundancyInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:49:38.870992+00:00
-- url     : https://prove2.me/theorems/b0ddd508-a00a-4efe-b2b6-1a13ec14a16b
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyInvariance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancySharpness
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

namespace PriceOfUniversality

open Finset Real

section Invariance

variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ Θ' : Type*} [Fintype Θ] [Nonempty Θ] [Fintype Θ'] [Nonempty Θ']

/-- The subclass of `p` obtained by reindexing along `e`: the sources that the
specialised decompressor still has to serve. -/
def subClass (p : Θ → A → ℝ) (e : Θ' → Θ) : Θ' → A → ℝ := fun t => p (e t)






end Invariance

/-! ## A one-source subclass, and the exact value of specialising -/

section Singleton

variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]



end Singleton

variable {m : ℕ}

/-- The one-source specialisation of the class of `m` deterministic sources. -/
noncomputable def indicatorSub (m : ℕ) [NeZero m] : Fin 1 → Fin m → ℝ :=
  subClass (indicatorClass m) (fun _ => (0 : Fin m))






end PriceOfUniversality


