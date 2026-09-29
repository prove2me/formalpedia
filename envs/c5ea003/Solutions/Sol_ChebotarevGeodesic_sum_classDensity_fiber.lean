-- Prove2me | solution 1 for ChebotarevGeodesic.sum_classDensity_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T20:47:12.392034+00:00
-- url     : https://prove2.me/submissions/4777a50a-845e-4f10-9f2e-dce059a4f1fa

-- Sol generated from Shared/ChebotarevGeodesicQuotient.lean
import Mathlib
import Definitions.Def_Shared_ChebotarevGeodesic
import Theorems.Thm_ChebotarevGeodesic_card_filter_preimage_mul_card
import Theorems.Thm_ChebotarevGeodesic_sum_classSize_fiber
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


omit [Fintype (ConjClasses G)] [DecidableEq G] in
/-- The preimage of a conjugacy class `D ⊆ H` under a surjective `f : G →* H` has
`|D| · |G| / |H|` elements. -/
theorem card_preimage_class_mul_card (f : G →* H) (hf : Surjective f) (D : ConjClasses H) :
    ({g : G | ConjClasses.mk (f g) = D} : Finset G).card * Fintype.card H
      = classSize H D * Fintype.card G := by
  classical
  have h1 : ({g : G | ConjClasses.mk (f g) = D} : Finset G)
      = ({g : G | f g ∈ ({h : H | ConjClasses.mk h = D} : Finset H)} : Finset G) := by
    ext g; simp
  rw [h1, card_filter_preimage_mul_card f hf]
  simp [classSize]









open ChebotarevGeodesic in
theorem solution(f : G →* H) (hf : Surjective f) (D : ConjClasses H) :
    ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
        classDensity G C
      = classDensity H D := by
  classical
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos (α := H)
  have hkey := card_preimage_class_mul_card f hf D
  have hsum := sum_classSize_fiber f D
  have hcast : (({g : G | ConjClasses.mk (f g) = D} : Finset G).card : ℝ) * Fintype.card H
      = (classSize H D : ℝ) * Fintype.card G := by exact_mod_cast hkey
  simp only [classDensity]
  rw [← Finset.sum_div]
  have : ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
      (classSize G C : ℝ)
      = (({g : G | ConjClasses.mk (f g) = D} : Finset G).card : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsum
  rw [this]
  field_simp
  linarith [hcast]
