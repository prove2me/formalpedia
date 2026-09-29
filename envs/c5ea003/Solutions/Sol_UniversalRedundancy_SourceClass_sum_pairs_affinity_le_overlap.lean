-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.sum_pairs_affinity_le_overlap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:22:39.924609+00:00
-- url     : https://prove2.me/submissions/418b3be6-785c-4f62-9a3d-e3a29bc10388

-- Sol generated from MachineLearning/UniversalRedundancy/Rigidity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_le
import Theorems.Thm_UniversalRedundancy_SourceClass_sum_min_eq_one_sub_tvDist
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






/-! ## Equality analysis of monotonicity (Part VII) -/



/-! ## A worked extremal family -/


variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]





/-! ## Equality analysis of the sufficient-statistic bound (Part II) -/

open SourceClass

variable {Θ : Type*} (S : SourceClass X Θ)





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
open UniversalRedundancy in
theorem solution{Θ : Type*} [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
    (S : SourceClass X Θ) :
    ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, (1 - tvDist (S.prob θ) (S.prob θ'))
      ≤ (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1) * S.overlap := by
  classical
  have hcard : ∀ θ : Θ, (((univ : Finset Θ).erase θ).card : ℝ) = (Fintype.card Θ : ℝ) - 1 := by
    intro θ
    rw [Finset.card_erase_of_mem (Finset.mem_univ θ), Finset.card_univ,
      Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero), Nat.cast_one]
  -- pointwise: the mass shared by two distinct sources fits in the non-maximal part
  have hpt : ∀ (x : X) (θ θ' : Θ), θ ≠ θ' →
      min (S.prob θ x) (S.prob θ' x) ≤ (∑ ϑ, S.prob ϑ x) - S.maxLik x := by
    intro x θ θ' hne
    obtain ⟨ϑ₀, hϑ₀⟩ := Finite.exists_max fun ϑ : Θ => S.prob ϑ x
    have hmax : S.maxLik x = S.prob ϑ₀ x :=
      le_antisymm (S.maxLik_le fun ϑ => hϑ₀ ϑ) (S.le_maxLik ϑ₀ x)
    have herase : (∑ ϑ, S.prob ϑ x) - S.prob ϑ₀ x = ∑ ϑ ∈ univ.erase ϑ₀, S.prob ϑ x := by
      have := Finset.add_sum_erase (univ : Finset Θ) (fun ϑ => S.prob ϑ x)
        (Finset.mem_univ ϑ₀)
      linarith
    have hpick : ∃ ϑ ∈ univ.erase ϑ₀, min (S.prob θ x) (S.prob θ' x) ≤ S.prob ϑ x := by
      by_cases h : θ = ϑ₀
      · exact ⟨θ', Finset.mem_erase.mpr ⟨fun hc => hne (h.trans hc.symm), Finset.mem_univ θ'⟩,
          min_le_right _ _⟩
      · exact ⟨θ, Finset.mem_erase.mpr ⟨h, Finset.mem_univ θ⟩, min_le_left _ _⟩
    obtain ⟨ϑ, hϑmem, hϑle⟩ := hpick
    have hsingle : S.prob ϑ x ≤ ∑ ϑ' ∈ univ.erase ϑ₀, S.prob ϑ' x :=
      Finset.single_le_sum (f := fun ϑ' => S.prob ϑ' x) (fun ϑ' _ => S.nonneg ϑ' x) hϑmem
    rw [hmax, herase]
    linarith
  -- one message at a time, summed over the `#Θ (#Θ - 1)` ordered pairs
  have hx : ∀ x : X, ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, min (S.prob θ x) (S.prob θ' x)
      ≤ (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1)
          * ((∑ ϑ, S.prob ϑ x) - S.maxLik x) := by
    intro x
    have hrow : ∀ θ : Θ, ∑ θ' ∈ univ.erase θ, min (S.prob θ x) (S.prob θ' x)
        ≤ ((Fintype.card Θ : ℝ) - 1) * ((∑ ϑ, S.prob ϑ x) - S.maxLik x) := by
      intro θ
      have hle : ∑ θ' ∈ univ.erase θ, min (S.prob θ x) (S.prob θ' x)
          ≤ ∑ _θ' ∈ univ.erase θ, ((∑ ϑ, S.prob ϑ x) - S.maxLik x) :=
        Finset.sum_le_sum fun θ' hθ' => hpt x θ θ' (Ne.symm (Finset.mem_erase.mp hθ').1)
      rwa [Finset.sum_const, nsmul_eq_mul, hcard θ] at hle
    have hsum := Finset.sum_le_sum fun (θ : Θ) (_ : θ ∈ (univ : Finset Θ)) => hrow θ
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc] at hsum
  calc ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, (1 - tvDist (S.prob θ) (S.prob θ'))
      = ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, ∑ x : X, min (S.prob θ x) (S.prob θ' x) :=
        Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun θ' _ =>
          (sum_min_eq_one_sub_tvDist (S.sum_one θ) (S.sum_one θ')).symm
    _ = ∑ x : X, ∑ θ : Θ, ∑ θ' ∈ univ.erase θ, min (S.prob θ x) (S.prob θ' x) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun θ _ => Finset.sum_comm
    _ ≤ ∑ x : X, (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1)
          * ((∑ ϑ, S.prob ϑ x) - S.maxLik x) := Finset.sum_le_sum fun x _ => hx x
    _ = (Fintype.card Θ : ℝ) * ((Fintype.card Θ : ℝ) - 1) * S.overlap := by
        unfold SourceClass.overlap
        rw [Finset.mul_sum]
