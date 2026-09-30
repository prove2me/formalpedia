-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clip_diameter_of_exterior_cap
-- name    : Hirsch.simultaneous_clip_diameter_of_exterior_cap
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T01:47:48.815005+00:00
-- url     : https://prove2.me/theorems/2e20b0a7-503c-4be4-bd9c-446b88f77c8e
-- title:
--   Exterior-cap witness bound for simultaneous clipping
-- statement:
--   Let R be a compact convex parent with a convex exterior-cap region G and a set V of old vertices. Assume every pair of vertices in V has a padded parent-edge route of length D, and every extreme point of R is either in V or is a cap vertex in G adjacent to some old vertex. If one point o in R strictly satisfies every added cut, G lies outside the final clip, and each final cut face i has intrinsic diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. The theorem deliberately assumes the exterior-cap witness/classification; it does not formalize existence of such a cap for every pointed H-polyhedron.
-- source:
--   Kernel- and standalone-verified theorem from jjoshua2/prove2me-work PR #52, source commit 5d57b93dc40d0f0917dcc99ce7a80274890c5c54.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clip_diameter_of_exterior_cap
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G V : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
    (o : EuclideanSpace ℝ (Fin d)) (ho : o ∈ R) (hs : ∀ i, f i o < b i)
    (hout : ∀ x ∈ G, x ∉ R ∩ {y | ∀ i, f i y ≤ b i})
    (D : ℕ)
    (hOld : ∀ a ∈ V, ∀ c ∈ V,
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = a ∧ w D = c ∧
        ∀ k < D, w k = w (k + 1) ∨ Adj R (w k) (w (k + 1)))
    (hclass : ∀ x ∈ extremePoints ℝ R,
      x ∈ V ∨ (x ∈ G ∧ ∃ a ∈ V, Adj R a x))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE ((R ∩ {y | ∀ j, f j y ≤ b j}) ∩ {x | f i x = b i}) (B i)) :
    DiamLE (R ∩ {y | ∀ i, f i y ≤ b i}) (D + 1 + ∑ i, B i) := by sorry

end Hirsch
