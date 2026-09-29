-- Prove2me | Theorems.Thm_TropicalShtarkov_shtarkovSum_le_card_image
-- name    : TropicalShtarkov.shtarkovSum_le_card_image
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:40:16.596645+00:00
-- url     : https://prove2.me/theorems/9f61088e-345e-4b6d-9963-5882e232ba35
-- title:
--   Sufficient-statistic upper bound.
-- statement:
--   **Sufficient-statistic upper bound.**  If the likelihood of every model at
--   `x` is dominated by `q (T x) x` for a family `q` of sub-probability measures
--   indexed by the values of a statistic `T`, then the Shtarkov sum is at most the
--   number of values the statistic takes.  This is the counting mechanism behind all
--   `(dimension/2)·log n` regret bounds.
--
--   ```lean
--   theorem TropicalShtarkov.shtarkovSum_le_card_image{Y : Type*} [DecidableEq Y] [Nonempty ι]
--       (P : ι → X → ℝ) (T : X → Y) (q : Y → X → ℝ)
--       (hdom : ∀ i x, P i x ≤ q (T x) x)
--       (hqnn : ∀ y x, 0 ≤ q y x)
--       (hqsum : ∀ y, ∑ x : X, q y x ≤ 1) :
--       shtarkovSum P ≤ (((univ : Finset X).image T).card : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Shtarkov/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Shtarkov/Basic.lean#L63

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

theorem TropicalShtarkov.shtarkovSum_le_card_image{Y : Type*} [DecidableEq Y] [Nonempty ι]
    (P : ι → X → ℝ) (T : X → Y) (q : Y → X → ℝ)
    (hdom : ∀ i x, P i x ≤ q (T x) x)
    (hqnn : ∀ y x, 0 ≤ q y x)
    (hqsum : ∀ y, ∑ x : X, q y x ≤ 1) :
    shtarkovSum P ≤ (((univ : Finset X).image T).card : ℝ) := by sorry
