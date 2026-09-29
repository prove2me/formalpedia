-- Prove2me | solution 1 for ChebotarevGeodesic.sum_classSize_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:46:03.425134+00:00
-- url     : https://prove2.me/submissions/fd968e4d-d51a-453a-af8b-c244a0d89fc2

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











open ChebotarevGeodesic in
omit [Fintype (ConjClasses H)] in
theorem solution(f : G →* H) (D : ConjClasses H) :
    ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
        classSize G C
      = ({g : G | ConjClasses.mk (f g) = D} : Finset G).card := by
  classical
  have hmaps : Set.MapsTo (fun g : G => ConjClasses.mk g)
      (({g : G | ConjClasses.mk (f g) = D} : Finset G) : Set G)
      ((({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G))) : Set _) := by
    intro g hg
    have hg' : ConjClasses.mk (f g) = D := by simpa using hg
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    show ConjClasses.map f (ConjClasses.mk g) = D
    simpa using hg'
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun g : G => ConjClasses.mk g)
    (s := ({g : G | ConjClasses.mk (f g) = D} : Finset G))
    (t := ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G))) hmaps
  rw [hcard]
  refine Finset.sum_congr rfl ?_
  intro C hC
  have hCD : ConjClasses.map f C = D := by simpa using hC
  have hset : ({g ∈ ({g : G | ConjClasses.mk (f g) = D} : Finset G) | ConjClasses.mk g = C})
      = ({g : G | ConjClasses.mk g = C} : Finset G) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, hg⟩; exact hg
    · intro hg
      refine ⟨?_, hg⟩
      have : ConjClasses.map f (ConjClasses.mk g) = D := by rw [hg]; exact hCD
      simpa using this
  rw [hset]
  simp [classSize]
