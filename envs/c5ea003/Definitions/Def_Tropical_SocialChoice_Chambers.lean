-- Prove2me | Definitions.Def_Tropical_SocialChoice_Chambers
-- name    : Tropical_SocialChoice_Chambers
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:44.381691+00:00
-- url     : https://prove2.me/theorems/564a828c-6df6-4770-b9a4-61360e939241
-- title:
--   Aether Catalog definitions — Tropical_SocialChoice_Chambers
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SocialChoice.Chambers`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SocialChoice/Chambers.lean by skeleton subtraction
import Mathlib
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

namespace TropicalChambers

open Finset

variable {ι : Type*}

/-- The tropical aggregator with support `S` and weights `δ`. -/
noncomputable def tropAgg (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) : (ι → ℝ) → ℝ :=
  fun x => S.inf' hS fun i => x i + δ i

/-- The chamber of profiles on which voter `i` attains the social score. -/
def chamber (S : Finset ι) (δ : ι → ℝ) (i : ι) : Set (ι → ℝ) :=
  {x | ∀ j ∈ S, x i + δ i ≤ x j + δ j}







end TropicalChambers


