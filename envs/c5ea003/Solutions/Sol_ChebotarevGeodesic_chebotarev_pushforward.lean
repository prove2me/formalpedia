-- Prove2me | solution 1 for ChebotarevGeodesic.chebotarev_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:48:51.038128+00:00
-- url     : https://prove2.me/submissions/7a15d2a6-e740-401e-8f98-65b30ba3de8b

-- Sol generated from Shared/ChebotarevGeodesicQuotient.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_HasErrorExponent_sum
import Theorems.Thm_ChebotarevGeodesic_sum_classDensity_fiber
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
theorem solution(f : G →* H) (hf : Surjective f)
    (piC : ConjClasses G → ℝ → ℝ) (li : ℝ → ℝ) (θ : ℝ)
    (h : ∀ C, HasErrorExponent (piC C) (fun x => classDensity G C * li x) θ) (D : ConjClasses H) :
    HasErrorExponent
      (fun x => ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
        piC C x)
      (fun x => classDensity H D * li x) θ := by
  classical
  have hsum := HasErrorExponent.sum
    (({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G))) piC
    (fun C x => classDensity G C * li x) θ (fun C _ => h C)
  have e : (fun x => ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} :
        Finset (ConjClasses G)), classDensity G C * li x)
      = fun x => classDensity H D * li x := by
    funext x
    rw [← Finset.sum_mul, sum_classDensity_fiber f hf D]
  rwa [e] at hsum
