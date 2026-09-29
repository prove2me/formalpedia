-- Prove2me | solution 1 for TropicalChambers.chamber_convex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:26.998923+00:00
-- url     : https://prove2.me/submissions/9d0f6089-7dca-463b-85e0-e1a659e5c5cc

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
theorem solution(S : Finset ι) (δ : ι → ℝ) (i : ι) :
    Convex ℝ (chamber S δ i) := by
  intro x hx y hy a b ha hb hab j hj
  have h1 := hx j hj
  have h2 := hy j hj
  have hxa : (a • x + b • y) i = a * x i + b * y i := rfl
  have hxb : (a • x + b • y) j = a * x j + b * y j := rfl
  rw [hxa, hxb]
  have hδi : a * δ i + b * δ i = δ i := by
    have h : (a + b) * δ i = δ i := by rw [hab, one_mul]
    linarith [h]
  have hδj : a * δ j + b * δ j = δ j := by
    have h : (a + b) * δ j = δ j := by rw [hab, one_mul]
    linarith [h]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
