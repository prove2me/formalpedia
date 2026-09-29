-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
-- name    : MachineLearning_UniversalRedundancy_Rigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:06:20.260722+00:00
-- url     : https://prove2.me/theorems/ef3fda5e-b412-4a2f-8dbf-3dd4cb19f04b
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Rigidity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Rigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Rigidity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
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

namespace UniversalRedundancy

namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)

/-! ## The conservation law -/

/-- The **overlap** of a finite source class: the total probability mass that
the sources share, `Ω = ∑ₓ (∑_θ p_θ x − sup_θ p_θ x)`. -/
noncomputable def overlap [Fintype Θ] : ℝ := ∑ x, ((∑ θ, S.prob θ x) - S.maxLik x)




/-! ## Rigidity at the upper endpoint -/

/-- The sources of the class are **mutually singular**: no message has positive
probability under two different sources. -/
def MutuallySingular : Prop :=
  ∀ (x : X) (θ θ' : Θ), θ ≠ θ' → S.prob θ x = 0 ∨ S.prob θ' x = 0





/-! ## Rigidity at the lower endpoint -/



end SourceClass

/-! ## The exact two-source formula -/

variable {X : Type*} [Fintype X]

/-- Total variation distance between two laws on a finite message space. -/
noncomputable def tvDist (p q : X → ℝ) : ℝ := (∑ x, |p x - q x|) / 2


namespace SourceClass










/-! ## Bit-level form of the two rigidity theorems -/



end SourceClass

/-! ## Equality analysis of the tied-product induction (Part VII) -/

variable {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]






/-! ## Equality analysis of monotonicity (Part VII) -/

/-- The subclass of `S` obtained by reindexing the parameter along `ι`. -/
def reindexClass {Θ Θ' : Type*} {Y : Type*} [Fintype Y] (S : SourceClass Y Θ) (ι : Θ' → Θ) :
    SourceClass Y Θ' where
  prob θ' x := S.prob (ι θ') x
  nonneg θ' x := S.nonneg (ι θ') x
  sum_one θ' := S.sum_one (ι θ')


/-! ## A worked extremal family -/

/-- The class of point masses on a finite alphabet: source `a` puts all its mass
on the message `a`.  It is the canonical mutually singular class. -/
noncomputable def pointMassClass (A : Type*) [Fintype A] [DecidableEq A] :
    SourceClass A A where
  prob a x := if x = a then 1 else 0
  nonneg a x := by by_cases h : x = a <;> simp [h]
  sum_one a := by simp

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]





/-! ## Equality analysis of the sufficient-statistic bound (Part II) -/

namespace SourceClass

variable {Θ : Type*} (S : SourceClass X Θ)



end SourceClass

end UniversalRedundancy

/-! ## Lab notes (exact rational experiments that guided this file)

Computed with `ℚ` arithmetic on explicit classes, `Cₛ = ∑ₓ max_θ p_θ x`:

* `p = (1/2, 1/3, 1/6)`, `q = (1/4, 1/4, 1/2)`:  `Cₛ = 4/3 = 1 + d_TV`.
* `p = (1, 0, 0)`,       `q = (0, 1/2, 1/2)`:    `Cₛ = 2   = 1 + d_TV` (singular).
* three copies of the uniform law on three letters: `Cₛ = 1`, overlap `Ω = 2`,
  so `Cₛ + Ω = 3 = #Θ`.
* all `8³ = 512` classes of three sources on three letters drawn from the
  palette `(1,0,0), (0,1,0), (0,0,1), (½,½,0), (½,0,½), (0,½,½), (⅓,⅓,⅓),
  (¼,¼,½)`: the predicate `Cₛ = 3` agreed with mutual singularity in every
  single case (0 disagreements) — the experiment behind
  `shtarkovSum_eq_card_iff_mutuallySingular`.
* tied product of two point-mass blocks on two letters: `Cₛ(tied) = 2` versus
  `Cₛ · Cₛ = 4` — the experiment behind `shtarkovSum_tiedProdClass_pointMass_lt`.
-/


