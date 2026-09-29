-- Prove2me | solution 1 for ChebotarevGeodesic.sum_classDensity_fiber_comp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:03:40.455135+00:00
-- url     : https://prove2.me/submissions/e8f8c866-3c59-4126-b2ad-e5d6e19295d0

-- Sol generated from Shared/ChebotarevGeodesicQuotient.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
/-
# Functoriality of the Chebotarev geodesic theorem under group quotients

Motivated by *"Chebotarev geodesic theorem: non-split case"*.  A Chebotarev-type statement is
attached to a finite Galois group `G` of a covering of the base (arithmetic) surface: for each
conjugacy class `C ⊆ G` one counts the primitive closed geodesics whose Frobenius class is `C`,
and the theorem asserts

  `π_C(x) = (|C|/|G|) · li(x) + O(x^{θ+ε})`.

An intermediate covering corresponds to a **surjective homomorphism** `f : G →* H`, and the
counting function of a class `D ⊆ H` is the sum of the counting functions of the `G`-classes
lying above it.  The purely arithmetic content of "the theorem for the top covering implies the
theorem for every intermediate covering" is the density identity

  `∑_{C ↦ D} |C|/|G| = |D|/|H|`,

i.e. the Chebotarev densities push forward along `ConjClasses.map f`.  This file proves that
identity from scratch (fibre counting for a surjective group homomorphism, plus the partition of
`G` into conjugacy classes) and deduces the analytic transfer statement, using the exponent
calculus of `ChebotarevGeodesic.lean`.

Main results:

* `card_filter_preimage_mul_card` : for a surjective `f : G →* H` and `S : Finset H`,
  `|f⁻¹ S| · |H| = |S| · |G|` (all fibres of `f` have the same cardinality);
* `sum_classSize_fiber` : `∑_{C ↦ D} |C| = |f⁻¹(D)|`;
* `sum_classDensity_fiber` : `∑_{C ↦ D} |C|/|G| = |D|/|H|`;
* `chebotarev_pushforward` : the Chebotarev geodesic theorem with exponent `θ` for `G` implies
  it with the *same* exponent `θ` for every quotient `H` of `G`;
* `chebotarev_pushforward_25_36` : the numerical instance of the paper;
* `chebotarev_pushforward_comp` : functoriality of the pushforward along a tower `G ↠ H ↠ K`.
-/


open Finset Filter Function

open ChebotarevGeodesic


variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Group H] [Fintype H] [DecidableEq H]


variable [Fintype (ConjClasses G)] [Fintype (ConjClasses H)]






omit [Fintype G] [DecidableEq G] [Fintype H] [DecidableEq H] [Fintype (ConjClasses G)]
  [Fintype (ConjClasses H)] in
/-- Compatibility of `ConjClasses.map` with composition of homomorphisms. -/
theorem conjClasses_map_comp {K : Type*} [Group K] (f : G →* H) (f' : H →* K)
    (C : ConjClasses G) :
    ConjClasses.map (f'.comp f) C = ConjClasses.map f' (ConjClasses.map f C) := by
  induction C using Quotient.inductionOn with
  | h g => rfl





open ChebotarevGeodesic in
theorem solution{K : Type*} [Group K] [Fintype K] [DecidableEq K]
    [Fintype (ConjClasses K)] (f : G →* H) (f' : H →* K) (E : ConjClasses K) :
    ∑ D ∈ ({D : ConjClasses H | ConjClasses.map f' D = E} : Finset (ConjClasses H)),
        ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
          classDensity G C
      = ∑ C ∈ ({C : ConjClasses G | ConjClasses.map (f'.comp f) C = E} :
          Finset (ConjClasses G)), classDensity G C := by
  classical
  have hcomp : ({C : ConjClasses G | ConjClasses.map (f'.comp f) C = E} : Finset (ConjClasses G))
      = ({C : ConjClasses G | ConjClasses.map f' (ConjClasses.map f C) = E} :
          Finset (ConjClasses G)) := by
    ext C
    simp [conjClasses_map_comp f f' C]
  rw [hcomp]
  -- regroup the sum over `C` according to the intermediate class `ConjClasses.map f C`
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := ({C : ConjClasses G | ConjClasses.map f' (ConjClasses.map f C) = E} :
      Finset (ConjClasses G)))
    (t := ({D : ConjClasses H | ConjClasses.map f' D = E} : Finset (ConjClasses H)))
    (g := fun C : ConjClasses G => ConjClasses.map f C)
    (f := fun C : ConjClasses G => classDensity G C)
    (by
      intro C hC
      have : ConjClasses.map f' (ConjClasses.map f C) = E := by simpa using hC
      simpa using this)]
  refine Finset.sum_congr rfl ?_
  intro D hD
  have hDE : ConjClasses.map f' D = E := by simpa using hD
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext C
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hCD
    exact ⟨by rw [hCD]; exact hDE, hCD⟩
  · rintro ⟨-, hCD⟩; exact hCD
