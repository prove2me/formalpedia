-- Prove2me | Theorems.Thm_UniversalRedundancy_shtarkovSum_tiedProdClass_lt_of_maxLik_lt
-- name    : UniversalRedundancy.shtarkovSum_tiedProdClass_lt_of_maxLik_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:51.479024+00:00
-- url     : https://prove2.me/theorems/cfa5c708-82a6-4372-a3c2-a14c17a64325
-- title:
--   Strictness from a single deficient outcome.
-- statement:
--   **Strictness from a single deficient outcome.**  If at one pair of block
--   outcomes the tied envelope falls strictly below the product of the block
--   envelopes, then tying the parameter strictly saves bits.  No finiteness of the
--   parameter space is needed, so this applies to continuous families such as the
--   memoryless simplex.
--
--   ```lean
--   theorem UniversalRedundancy.shtarkovSum_tiedProdClass_lt_of_maxLik_lt{Θ : Type*} [Nonempty Θ]
--       (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) {x₁ : X₁} {x₂ : X₂}
--       (h : (tiedProdClass S₁ S₂).maxLik (x₁, x₂) < S₁.maxLik x₁ * S₂.maxLik x₂) :
--       (tiedProdClass S₁ S₂).shtarkovSum < S₁.shtarkovSum * S₂.shtarkovSum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/Rigidity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/Rigidity.lean#L554

-- Thm stub generated from MachineLearning/UniversalRedundancy/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality VIII: rigidity — the equality cases

Eighth instalment of the thread *Compression Beyond the Pigeonhole Bound*.
Parts I–VII established the two *sharp bounds* for the Shtarkov sum of a finite
source class,

`1 ≤ Cₛ ≤ #Θ`,

together with the closure laws that keep a class inside the `1`-sum (simplex)
world: products, tied products, reindexings.  Both endpoints were known to be
*attained* (`shtarkovSum_of_subsingleton`, `shtarkovSum_eq_card_of_disjoint_supports`).
What was missing is the **equality analysis**: which classes sit exactly at an
endpoint, and how far a class is from an endpoint when it misses it.

## Central Idea

The whole rigidity picture follows from a single *exact identity* that upgrades
the inequality `Cₛ ≤ #Θ` to a conservation law:

`Cₛ + Ω = #Θ`,   where   `Ω = ∑ₓ (∑_θ p_θ x − sup_θ p_θ x) ≥ 0`

is the **overlap** of the class — the probability mass that the sources share.
Every equality statement below is read off from `Ω`:

* `Ω = 0` ⟺ the sources are mutually singular ⟺ `Cₛ = #Θ` (maximal price);
* at the other end, `Cₛ = 1` forces `p_θ = sup_θ p_θ` pointwise, i.e. *all*
  sources coincide — no non-trivial class is free;
* for a two-source class the identity becomes the exact formula
  `Cₛ = 1 + d_TV(p, q)`, so the price of universality of a pair is *literally*
  the total variation distance, interpolating between the two rigid endpoints;
* consequently `1 + max_{θ≠θ'} d_TV(p_θ, p_θ') ≤ Cₛ` for every class: pairwise
  statistical separation is a lower bound on the universality price.

The same "sum of a pointwise inequality" analysis, applied to the *induction*
behind the tied-product law of Part VII, produces the equality criterion for
subadditivity: sharing a parameter across two blocks costs the full additive
price iff every pair of block outcomes admits a **common maximiser**.

## Main Results

* `SourceClass.overlap`, `shtarkovSum_add_overlap_eq_card` — the conservation law
* `SourceClass.MutuallySingular`, `shtarkovSum_eq_card_iff_mutuallySingular` —
  the upper endpoint is rigid
* `shtarkovSum_lt_card_of_overlap` — any shared message strictly lowers the price
* `shtarkovSum_eq_card_iff_exists_supports` — iff-form of Part I's partition
  criterion (`shtarkovSum_eq_card_of_disjoint_supports` is the easy direction)
* `shtarkovSum_eq_one_iff_forall_eq` — the lower endpoint is rigid: converse of
  the calibration law `shtarkovSum_of_subsingleton`
* `logb_shtarkovSum_eq_zero_iff`, `logb_shtarkovSum_eq_logb_card_iff` — the two
  rigidity theorems in bits
* `tvDist`, `shtarkovSum_pair_eq_one_add_tvDist` — exact two-source formula
* `one_add_tvDist_le_shtarkovSum`, `shtarkovSum_le_one_add_sum_tvDist` —
  a total-variation sandwich for the price of any class
* `shtarkovSum_le_card_sub_one_add_tvDist` — quantitative stability: one close
  pair already pulls the price away from the maximum
* `sum_pairs_affinity_le_overlap`, `shtarkovSum_le_card_sub_avg_affinity` —
  all-pairs stability: the average pairwise affinity is a deficit from the
  maximal price
* `reindexClass`, `shtarkovSum_reindexClass_eq_iff` — equality case of the
  monotonicity law
* `shtarkovSum_tiedProdClass_eq_iff` — equality analysis of the tied-product
  induction of Part VII, and `shtarkovSum_tiedProdClass_lt` for the strict case
* `pointMassClass`, `shtarkovSum_pointMassClass`,
  `shtarkovSum_tiedProdClass_pointMass` — a worked extremal family witnessing
  both endpoints and strict subadditivity
* `sum_maxLik_fiber_le_one`, `shtarkovSum_eq_card_statistic_iff` — equality
  analysis of the sufficient-statistic bound of Part II

## Application Keywords

universal coding, Shtarkov sum, rigidity, equality case, total variation,
mutual singularity, subadditivity, method of types
-/


open Finset Real

open UniversalRedundancy

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)

/-! ## The conservation law -/





/-! ## Rigidity at the upper endpoint -/






/-! ## Rigidity at the lower endpoint -/




/-! ## The exact two-source formula -/

variable {X : Type*} [Fintype X]



open SourceClass










/-! ## Bit-level form of the two rigidity theorems -/




/-! ## Equality analysis of the tied-product induction (Part VII) -/

variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]

theorem UniversalRedundancy.shtarkovSum_tiedProdClass_lt_of_maxLik_lt{Θ : Type*} [Nonempty Θ]
    (S₁ : SourceClass X₁ Θ) (S₂ : SourceClass X₂ Θ) {x₁ : X₁} {x₂ : X₂}
    (h : (tiedProdClass S₁ S₂).maxLik (x₁, x₂) < S₁.maxLik x₁ * S₂.maxLik x₂) :
    (tiedProdClass S₁ S₂).shtarkovSum < S₁.shtarkovSum * S₂.shtarkovSum := by sorry
