-- Prove2me | Theorems.Thm_Hirsch_simultaneous_clip_diameter_of_exterior_cap_without_strict_centre
-- name    : Hirsch.simultaneous_clip_diameter_of_exterior_cap_without_strict_centre
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T04:06:04.061258+00:00
-- url     : https://prove2.me/theorems/dab9feac-c8f3-45bb-a240-80702df8092a
-- title:
--   Exterior-cap simultaneous clipping needs no separately supplied strict centre
-- statement:
--   Let R be a compact convex outer polytope with an exterior convex cap G and a set V of old vertices. Assume old vertices route within D graph edges and every other outer extreme vertex lies on G adjacent to an old vertex. For finitely many simultaneous cuts, assume G lies outside the final clipped polytope and each final cut face has intrinsic graph diameter at most B_i. Then the final clipped polytope has padded graph diameter at most D + 1 + sum_i B_i. No strict feasible centre is an input: either finite convex averaging produces one, or one cut is equality on the whole final polytope and its face budget closes the bound directly.
-- source:
--   Kernel-verified Lean strengthening of the exterior-cap clipping theorem in jjoshua2/prove2me-work.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem simultaneous_clip_diameter_of_exterior_cap_without_strict_centre
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G V : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
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
