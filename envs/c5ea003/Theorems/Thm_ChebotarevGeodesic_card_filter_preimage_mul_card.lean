-- Prove2me | Theorems.Thm_ChebotarevGeodesic_card_filter_preimage_mul_card
-- name    : ChebotarevGeodesic.card_filter_preimage_mul_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:19:41.737196+00:00
-- url     : https://prove2.me/theorems/f3fd83ec-17c3-42af-8e1d-faf973141864
-- title:
--   All fibres of a group homomorphism over its image have the same size; consequently, for a
-- statement:
--   All fibres of a group homomorphism over its image have the same size; consequently, for a
--   **surjective** `f : G â* H` and any `S : Finset H`, the preimage of `S` has cardinality
--   `|S| Â· |G| / |H|`.  Stated multiplicatively to stay inside `â`.
--
--   ```lean
--   theorem ChebotarevGeodesic.card_filter_preimage_mul_card(f : G →* H) (hf : Surjective f) (S : Finset H) :
--       ({g : G | f g ∈ S} : Finset G).card * Fintype.card H
--         = S.card * Fintype.card G := by sorry
--   variable [Fintype (ConjClasses G)] [Fintype (ConjClasses H)]
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicQuotient.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicQuotient.lean#L47

-- Thm stub generated from Shared/ChebotarevGeodesicQuotient.lean
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

omit [DecidableEq G] in

theorem ChebotarevGeodesic.card_filter_preimage_mul_card(f : G →* H) (hf : Surjective f) (S : Finset H) :
    ({g : G | f g ∈ S} : Finset G).card * Fintype.card H
      = S.card * Fintype.card G := by sorry
