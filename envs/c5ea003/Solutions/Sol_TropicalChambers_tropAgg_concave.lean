-- Prove2me | solution 1 for TropicalChambers.tropAgg_concave
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:35:27.609753+00:00
-- url     : https://prove2.me/submissions/918b88ca-1dd3-4f2d-92f3-00812e23cdf2

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
theorem solution(S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) :
    ConcaveOn ℝ Set.univ (tropAgg S hS δ) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  refine Finset.le_inf' hS _ ?_
  intro j hj
  have hxj : (a • x + b • y) j = a * x j + b * y j := rfl
  have h1 : tropAgg S hS δ x ≤ x j + δ j := Finset.inf'_le (fun k => x k + δ k) hj
  have h2 : tropAgg S hS δ y ≤ y j + δ j := Finset.inf'_le (fun k => y k + δ k) hj
  rw [hxj]
  have hδ : a * δ j + b * δ j = δ j := by
    have h : (a + b) * δ j = δ j := by rw [hab, one_mul]
    linarith [h]
  simp only [smul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
