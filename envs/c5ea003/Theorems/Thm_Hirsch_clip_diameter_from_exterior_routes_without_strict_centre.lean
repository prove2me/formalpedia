-- Prove2me | Theorems.Thm_Hirsch_clip_diameter_from_exterior_routes_without_strict_centre
-- name    : Hirsch.clip_diameter_from_exterior_routes_without_strict_centre
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T04:09:01.486801+00:00
-- url     : https://prove2.me/theorems/cd2c22ce-d5f7-4db4-a6b5-637d61813ff0
-- title:
--   Exterior shortcuts plus final cut-face budgets transfer diameter without a strict centre
-- statement:
--   Let R be a compact convex outer polytope and G a convex exterior region contained in R but disjoint from the final simultaneously clipped polytope. Assume every pair of outer extreme vertices has a padded D-step route whose steps are either true R-edges or arbitrary jumps with both endpoints in G. If final cut face i has intrinsic graph diameter at most B_i, then the final clipped polytope has padded graph diameter at most D + sum_i B_i. No strict feasible centre is assumed: finite averaging produces one unless a cut is equality everywhere, in which case its face budget bounds the whole final polytope directly.
-- source:
--   Kernel-verified generic exterior-route transfer in jjoshua2/prove2me-work.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem clip_diameter_from_exterior_routes_without_strict_centre
    {d : ℕ} {ι : Type*} [Fintype ι]
    (R G : Set (EuclideanSpace ℝ (Fin d)))
    (hR : Convex ℝ R) (hRc : IsCompact R)
    (hG : Convex ℝ G) (hGR : G ⊆ R)
    (f : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (b : ι → ℝ)
    (hout : ∀ x ∈ G, x ∉ R ∩ {y | ∀ i, f i y ≤ b i})
    (D : ℕ)
    (hD : ∀ a ∈ extremePoints ℝ R, ∀ c ∈ extremePoints ℝ R,
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = a ∧ w D = c ∧
        ∀ k < D,
          w k = w (k + 1) ∨
            (Adj R (w k) (w (k + 1)) ∨ (w k ∈ G ∧ w (k + 1) ∈ G)))
    (B : ι → ℕ)
    (hB : ∀ i, DiamLE ((R ∩ {y | ∀ j, f j y ≤ b j}) ∩ {x | f i x = b i}) (B i)) :
    DiamLE (R ∩ {y | ∀ i, f i y ≤ b i}) (D + ∑ i, B i) := by sorry

end Hirsch
