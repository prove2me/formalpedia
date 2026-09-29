-- Prove2me | solution 1 for mme_modern_complete_split_interval_acceptance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T17:23:53.360804+00:00
-- url     : https://prove2.me/submissions/800d711c-2d42-4ab4-8782-ab37fab986fe

import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

open BigOperators

universe u v w

private theorem three_coordinate_sum_min_mono
    {I : Type u} [Fintype I] (lo actual : I → Fin 3 → ℝ)
    (h : ∀ i d, lo i d ≤ actual i d) :
    min (∑ i, lo i 0) (min (∑ i, lo i 1) (∑ i, lo i 2)) ≤
      min (∑ i, actual i 0) (min (∑ i, actual i 1) (∑ i, actual i 2)) := by
  have hsum (d : Fin 3) : (∑ i, lo i d) ≤ ∑ i, actual i d :=
    Finset.sum_le_sum fun i _ ↦ h i d
  exact min_le_min (hsum 0) (min_le_min (hsum 1) (hsum 2))

/-- Source-shaped directed-interval acceptance for AlphaEvolve Equation (11).
Each retained group takes a minimum AFTER summing its node contributions.
The margin is preserved exactly; zero margin recovers non-strict feasibility.
No entropy, numerical feasibility, or tensor extraction is assumed here. -/
theorem solution
    {G : Type u} {I : G → Type v} {J : Type w}
    [Fintype G] [∀ g, Fintype (I g)] [Fintype J]
    (weight : G → ℝ)
    (nodeLower nodeActual : (g : G) → I g → Fin 3 → ℝ)
    (leafLower leafActual : J → Fin 3 → ℝ)
    (Omega scale logActual logUpper margin : ℝ)
    (hweight : ∀ g, 0 ≤ weight g)
    (hnode : ∀ g i d, nodeLower g i d ≤ nodeActual g i d)
    (hleaf : ∀ j d, leafLower j d ≤ leafActual j d)
    (hOmega : 0 ≤ Omega) (hscale : 0 ≤ scale)
    (hlog : logActual ≤ logUpper)
    (hcertificate :
      scale * logUpper + margin ≤
        (∑ g, weight g *
          min (∑ i, nodeLower g i 0)
            (min (∑ i, nodeLower g i 1) (∑ i, nodeLower g i 2))) +
        min (∑ j, leafLower j 0)
          (min (∑ j, leafLower j 1) (∑ j, leafLower j 2)) * Omega) :
    scale * logActual + margin ≤
      (∑ g, weight g *
        min (∑ i, nodeActual g i 0)
          (min (∑ i, nodeActual g i 1) (∑ i, nodeActual g i 2))) +
      min (∑ j, leafActual j 0)
        (min (∑ j, leafActual j 1) (∑ j, leafActual j 2)) * Omega := by
  have hretained :
      (∑ g, weight g *
        min (∑ i, nodeLower g i 0)
          (min (∑ i, nodeLower g i 1) (∑ i, nodeLower g i 2))) ≤
      ∑ g, weight g *
        min (∑ i, nodeActual g i 0)
          (min (∑ i, nodeActual g i 1) (∑ i, nodeActual g i 2)) := by
    apply Finset.sum_le_sum
    intro g _
    exact mul_le_mul_of_nonneg_left
      (three_coordinate_sum_min_mono (nodeLower g) (nodeActual g) (hnode g))
      (hweight g)
  have hmatrix := three_coordinate_sum_min_mono leafLower leafActual hleaf
  exact (add_le_add (mul_le_mul_of_nonneg_left hlog hscale) (le_refl margin)).trans
    (hcertificate.trans (add_le_add hretained
      (mul_le_mul_of_nonneg_right hmatrix hOmega)))
