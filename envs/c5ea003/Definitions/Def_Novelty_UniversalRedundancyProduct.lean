-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyProduct
-- name    : Novelty_UniversalRedundancyProduct
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:47:14.843329+00:00
-- url     : https://prove2.me/theorems/1e8d3306-6f93-4909-a91c-da1bbb011b8d
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyProduct
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyProduct`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyProduct.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyBernoulli
/-
# The price of universality, V: additivity over independent components

The minimax regret of a class of sources was computed exactly in
`UniversalRedundancyShtarkov.lean` as `log₂ S`, `S` the Shtarkov sum.  Here we
show that the Shtarkov sum is **multiplicative** over independent products of
classes,

  `S(P ⊗ Q) = S(P) · S(Q)`,

so that the price of universality is **additive**:

  `regret(P ⊗ Q) = regret(P) + regret(Q)`.

Together with the `(1/2) log₂ n` bound of `UniversalRedundancyBernoulli.lean`
this yields the `k`-parameter Rissanen rate: a class of `k` independent
memoryless binary blocks of length `n` forces every code to pay at least
`k · ((1/2) log₂ n − 2)` bits of regret.  We prove the case `k = 2` explicitly
(`two_block_bernoulli_regret`), which already exhibits the linear-in-`k` growth
that makes the price of universality unbounded as models get richer.

The structural moral for the research programme: *the shared decompressor must
carry one independent "parameter description" per independent component of the
model class; specialisation buys back exactly that amount and no more.*
-/

namespace PriceOfUniversality

open Finset Real

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
variable {Θ Ψ : Type*} [Fintype Θ] [Fintype Ψ] [Nonempty Θ] [Nonempty Ψ]

/-- The independent product of two source classes: parameters and messages are
paired, and probabilities multiply. -/
noncomputable def prodClass (p : Θ → A → ℝ) (q : Ψ → B → ℝ) : Θ × Ψ → A × B → ℝ :=
  fun t x => p t.1 x.1 * q t.2 x.2






end PriceOfUniversality


