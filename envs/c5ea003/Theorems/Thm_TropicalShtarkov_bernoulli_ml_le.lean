-- Prove2me | Theorems.Thm_TropicalShtarkov_bernoulli_ml_le
-- name    : TropicalShtarkov.bernoulli_ml_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:40:21.604204+00:00
-- url     : https://prove2.me/theorems/f7c4d480-0cd0-4978-8647-c0e44d57c2d4
-- title:
--   Bernoulli maximum-likelihood inequality.
-- statement:
--   **Bernoulli maximum-likelihood inequality.**
--
--   ```lean
--   theorem TropicalShtarkov.bernoulli_ml_le(a b : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
--       θ ^ a * (1 - θ) ^ b ≤ mlParam a b ^ a * (1 - mlParam a b) ^ b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Shtarkov/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Shtarkov/Basic.lean#L141

-- Thm stub generated from Tropical/Shtarkov/Basic.lean
import Mathlib
import Definitions.Def_Tropical_Shtarkov_Basic
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

open TropicalShtarkov

/-! ## The Shtarkov sum -/

variable {X ι : Type*} [Fintype X]







/-! ## The one-dimensional maximum-likelihood inequality

For a Bernoulli source observed `a` times as `true` and `b` times as `false`,
the likelihood `θ^a (1-θ)^b` is maximised at the empirical frequency
`a / (a+b)`.  This is the analytic core of the finite-state upper bound; the
proof is the Gibbs/`log x ≤ x - 1` argument. -/

theorem TropicalShtarkov.bernoulli_ml_le(a b : ℕ) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    θ ^ a * (1 - θ) ^ b ≤ mlParam a b ^ a * (1 - mlParam a b) ^ b := by sorry
