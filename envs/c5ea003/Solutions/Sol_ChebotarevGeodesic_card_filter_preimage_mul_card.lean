-- Prove2me | solution 1 for ChebotarevGeodesic.card_filter_preimage_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:58:59.605741+00:00
-- url     : https://prove2.me/submissions/ea72b484-c3bf-4adc-a5f3-9747a798524f

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













open ChebotarevGeodesic in
omit [DecidableEq G] in
theorem solution(f : G →* H) (hf : Surjective f) (S : Finset H) :
    ({g : G | f g ∈ S} : Finset G).card * Fintype.card H
      = S.card * Fintype.card G := by
  classical
  -- every fibre has the same cardinality `N`
  set N : ℕ := ({g : G | f g = 1} : Finset G).card with hN
  have hfib : ∀ h : H, ({g : G | f g = h} : Finset G).card = N := by
    intro h
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf h) ⟨1, map_one f⟩
  -- cardinality of a preimage
  have hpre : ∀ S : Finset H, ({g : G | f g ∈ S} : Finset G).card = S.card * N := by
    intro S
    have hmaps : Set.MapsTo (fun g : G => f g) (({g : G | f g ∈ S} : Finset G) : Set G)
        (S : Set H) := by
      intro g hg
      simpa using (by simpa using hg : f g ∈ S)
    have := Finset.card_eq_sum_card_fiberwise (f := fun g : G => f g)
      (s := ({g : G | f g ∈ S} : Finset G)) (t := S) hmaps
    rw [this]
    have hcong : ∀ h ∈ S,
        ({g ∈ ({g : G | f g ∈ S} : Finset G) | f g = h}).card = N := by
      intro h hh
      have : ({g ∈ ({g : G | f g ∈ S} : Finset G) | f g = h}) = ({g : G | f g = h} : Finset G) := by
        ext g
        simp only [Finset.mem_filter, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, hg⟩; exact hg
        · intro hg; exact ⟨by rw [hg]; exact hh, hg⟩
      rw [this, hfib]
    rw [Finset.sum_congr rfl hcong, Finset.sum_const, smul_eq_mul]
  -- the total count gives `|G| = |H| * N`
  have htot : Fintype.card G = Fintype.card H * N := by
    have h1 : ({g : G | f g ∈ (Finset.univ : Finset H)} : Finset G) = Finset.univ := by
      ext g; simp
    have := hpre (Finset.univ : Finset H)
    rw [h1, Finset.card_univ, Finset.card_univ] at this
    exact this
  rw [hpre S, htot]
  ring
