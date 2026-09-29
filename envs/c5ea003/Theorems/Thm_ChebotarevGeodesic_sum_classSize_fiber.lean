-- Prove2me | Theorems.Thm_ChebotarevGeodesic_sum_classSize_fiber
-- name    : ChebotarevGeodesic.sum_classSize_fiber
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:20:28.166786+00:00
-- url     : https://prove2.me/theorems/54623ef6-8fe0-428a-94b2-64844f86a6ab
-- title:
--   The `G`-conjugacy classes lying above a fixed `H`-conjugacy class `D` partition the
-- statement:
--   The `G`-conjugacy classes lying above a fixed `H`-conjugacy class `D` partition the
--   preimage of `D`.
--
--   ```lean
--   theorem ChebotarevGeodesic.sum_classSize_fiber(f : G →* H) (D : ConjClasses H) :
--       ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
--           classSize G C
--         = ({g : G | ConjClasses.mk (f g) = D} : Finset G).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/ChebotarevGeodesicQuotient.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/ChebotarevGeodesicQuotient.lean#L93

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


variable [Fintype (ConjClasses G)] [Fintype (ConjClasses H)]

omit [Fintype (ConjClasses H)] in

theorem ChebotarevGeodesic.sum_classSize_fiber(f : G →* H) (D : ConjClasses H) :
    ∑ C ∈ ({C : ConjClasses G | ConjClasses.map f C = D} : Finset (ConjClasses G)),
        classSize G C
      = ({g : G | ConjClasses.mk (f g) = D} : Finset G).card := by sorry
