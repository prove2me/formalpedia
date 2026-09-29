-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyPi
-- name    : Novelty_UniversalRedundancyPi
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:50:19.245718+00:00
-- url     : https://prove2.me/theorems/6072bbe3-8f9f-477a-a9fd-48141b5acd86
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyPi
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyPi`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyPi.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
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

namespace PriceOfUniversality

open Finset Real

section PiClass

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : ι → Type*} [∀ i, Fintype (A i)]
variable {Θ : ι → Type*} [∀ i, Fintype (Θ i)] [∀ i, Nonempty (Θ i)]

/-- The independent product of a finite family of source classes: parameters and
messages are tuples, and probabilities multiply coordinatewise. -/
noncomputable def piClass (p : ∀ i, Θ i → A i → ℝ) : (∀ i, Θ i) → (∀ i, A i) → ℝ :=
  fun t x => ∏ i, p i (t i) (x i)






end PiClass

/-! ## The `k`-parameter Rissanen rate for memoryless binary blocks -/

/-- The class of `k` independent memoryless binary sources, each emitting a block
of `n` bits with its own bias. -/
noncomputable def kBernClass (k n : ℕ) :
    (Fin k → Fin (n + 1)) → (Fin k → Msg n) → ℝ :=
  piClass (A := fun _ : Fin k => Msg n) (Θ := fun _ : Fin k => Fin (n + 1))
    (fun _ => bernClass n)







end PriceOfUniversality


