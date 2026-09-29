-- Prove2me | solution 1 for TropicalChambers.mem_chamber_of_eq_inf_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T20:24:05.636917+00:00
-- url     : https://prove2.me/submissions/5e8338ba-9f76-4c06-b145-ca73192e15b5

-- Sol generated from Tropical/SocialChoice/Chambers.lean
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










open TropicalChambers in
theorem solution{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) {x : ι → ℝ}
    {i : ι} (hi : tropAgg S hS δ x = x i + δ i) : x ∈ chamber S δ i := by
  intro j hj
  rw [← hi]
  exact Finset.inf'_le (fun k => x k + δ k) hj
