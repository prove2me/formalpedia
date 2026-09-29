-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyMinimax
-- name    : Novelty_UniversalRedundancyMinimax
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:45:14.86392+00:00
-- url     : https://prove2.me/theorems/c8e680b3-01ec-40d1-8100-743559c11f79
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyMinimax
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyMinimax`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyMinimax.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
/-
# The price of universality, II: minimax redundancy and mutual information

A *universal* code must serve every source in a class `{p θ}` with a single
length function `L`, whereas a *specialised* code may be tuned to one source.
The number of extra bits this costs is the **price of universality**.

Main results of this file, for a finite class `Θ` of sources on a finite
alphabet `A`:

* `kl_compensation` — the exact decomposition
  `∑ θ, π θ * D(p θ ‖ q) = I(π) + D(mixture ‖ q)`, valid for every coding
  distribution `q`. This is the algebraic heart of the redundancy-capacity
  theorem.
* `exists_source_redundancy_ge_mutualInfo` — **lower bound**: whatever code is
  used, some source in the class pays at least the mutual information `I(π)`
  of any prior `π`.
* `price_of_universality_upper` — **upper bound**: the Shannon code built from
  the mixture pays at most `log₂ |Θ| + 1` bits on *every* source of the class.
* `price_of_universality_sandwich` — for a class of `m` sources with pairwise
  disjoint supports the minimax redundancy is exactly `log₂ m`, up to one bit:
  `log₂ m ≤ minimax redundancy ≤ log₂ m + 1`.

The last statement is the promised closed form: the price of universality over
a class of `m` mutually distinguishable sources is `log₂ m` bits, i.e. exactly
the number of bits needed to name the source — no more and no less.
-/

namespace PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] {Θ : Type*} [Fintype Θ]

/-! ## Mixtures and mutual information -/

/-- The Bayes mixture `∑ θ π θ • p θ` of a class of sources under a prior. -/
noncomputable def mixture (pri : Θ → ℝ) (p : Θ → A → ℝ) : A → ℝ :=
  fun a => ∑ θ, pri θ * p θ a

/-- The mutual information between the source index and the message, i.e. the
average divergence of the class members from the mixture. -/
noncomputable def mutualInfo (pri : Θ → ℝ) (p : Θ → A → ℝ) : ℝ :=
  ∑ θ, pri θ * kl (p θ) (mixture pri p)




/-! ## The compensation identity -/


/-! ## The lower bound: universality costs at least the mutual information -/



/-! ## The upper bound: the mixture code -/




/-! ## Exact price for a class of mutually distinguishable sources -/

/-- A family of sources has *disjoint supports* when no message is possible under
two different members: the sources are perfectly distinguishable from one
observation. -/
def DisjointSupports (p : Θ → A → ℝ) : Prop :=
  ∀ θ θ' : Θ, ∀ a : A, θ ≠ θ' → 0 < p θ a → p θ' a = 0



end PriceOfUniversality


