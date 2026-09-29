-- Prove2me | Theorems.Thm_TropicalChambers_tropAgg_concave
-- name    : TropicalChambers.tropAgg_concave
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:07.255003+00:00
-- url     : https://prove2.me/theorems/d671d543-1ca2-4bbe-b840-4e6636f73e66
-- title:
--   A min-plus aggregator is concave: it is a minimum of affine functions.
-- statement:
--   A min-plus aggregator is concave: it is a minimum of affine functions.
--
--   ```lean
--   theorem TropicalChambers.tropAgg_concave(S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) :
--       ConcaveOn ℝ Set.univ (tropAgg S hS δ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SocialChoice/Chambers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SocialChoice/Chambers.lean#L82

-- Thm stub generated from Tropical/SocialChoice/Chambers.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_Chambers
/-
# Polyhedral chambers of social decisiveness

The third face of the tropical/social-choice bridge: the *geometry* of a
min-plus aggregator `F x = min_{i ∈ S} (x i + δ i)`.

For each voter `i` in the tropical support `S` the set of profiles on which `i`
attains the social score is the **chamber**

`chamber S δ i = {x | ∀ j ∈ S, x i + δ i ≤ x j + δ j}`,

an intersection of half-spaces.  The chambers are convex polyhedra, they cover
the whole profile space, `F` is affine (indeed a coordinate projection shifted
by a constant) on each of them, and two chambers meet exactly along the wall
where the two tropical monomials agree.  Finally `F` itself is concave, being a
minimum of affine functions.

Main results: `chamber_convex`, `mem_chamber_of_eq_inf'`, `iUnion_chamber`,
`tropAgg_eq_on_chamber`, `wall_eq`, `tropAgg_concave`.
-/

open TropicalChambers

open Finset

variable {ι : Type*}

theorem TropicalChambers.tropAgg_concave(S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) :
    ConcaveOn ℝ Set.univ (tropAgg S hS δ) := by sorry
