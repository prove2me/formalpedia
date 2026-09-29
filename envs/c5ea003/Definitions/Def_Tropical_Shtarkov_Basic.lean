-- Prove2me | Definitions.Def_Tropical_Shtarkov_Basic
-- name    : Tropical_Shtarkov_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:43.725917+00:00
-- url     : https://prove2.me/theorems/16e1a892-04db-4e97-9974-8c13bd2df705
-- title:
--   Aether Catalog definitions — Tropical_Shtarkov_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Shtarkov.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Shtarkov/Basic.lean by skeleton subtraction
import Mathlib
/-
# Tropical Shtarkov Sums: the abstract layer

## Bridge: max-plus (tropical) algebra ↔ universal source coding ↔ counting

The *Shtarkov sum* (a.k.a. the normalizing constant of the normalized maximum
likelihood distribution) of a model class `{P i}` on a finite sample space `X` is

  `S(P) = ∑_{x ∈ X} sup_i P i x`.

The inner `sup` is exactly a **tropical (max-plus) sum** of the log-likelihoods:
`log sup_i P i x = ⊕_i log P i x`, so `S(P)` is the classical mass of the
tropicalisation of the class, and `log S(P)` is the minimax pointwise regret of
the class.  This file develops the two structural tools used throughout:

* `shtarkovSum_ge_packing` — a *packing* lower bound: any collection of
  (sample, model) pairs contributes to `S`;
* `shtarkovSum_le_card_image` — a *sufficient statistic* upper bound: if the
  pointwise supremum is dominated by a sub-probability measure depending on `x`
  only through a statistic `T`, then `S ≤ |image T|`.

Together with the one-dimensional maximum-likelihood inequality
`bernoulli_ml_le` these give matching upper/lower bounds for finite-state
classes in `Catalog/Tropical/Shtarkov/FiniteState.lean`.
-/


open Finset

namespace TropicalShtarkov

/-! ## The Shtarkov sum -/

variable {X ι : Type*} [Fintype X]

/-- The Shtarkov sum (NML normalizer) of a family of densities `P : ι → X → ℝ`
on a finite sample space `X`.  Its logarithm is the minimax pointwise regret. -/
noncomputable def shtarkovSum (P : ι → X → ℝ) : ℝ := ∑ x : X, ⨆ i, P i x






/-! ## The one-dimensional maximum-likelihood inequality

For a Bernoulli source observed `a` times as `true` and `b` times as `false`,
the likelihood `θ^a (1-θ)^b` is maximised at the empirical frequency
`a / (a+b)`.  This is the analytic core of the finite-state upper bound; the
proof is the Gibbs/`log x ≤ x - 1` argument. -/

/-- The maximum-likelihood Bernoulli parameter for `a` successes and `b`
failures (with the convention `0` for the empty sample). -/
noncomputable def mlParam (a b : ℕ) : ℝ := if a + b = 0 then 0 else (a : ℝ) / (a + b)





end TropicalShtarkov


