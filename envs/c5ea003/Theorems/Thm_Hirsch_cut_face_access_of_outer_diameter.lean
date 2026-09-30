-- Prove2me | Theorems.Thm_Hirsch_cut_face_access_of_outer_diameter
-- name    : Hirsch.cut_face_access_of_outer_diameter
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T21:06:54.019069+00:00
-- url     : https://prove2.me/theorems/7d78c1ee-f7f7-439b-99f9-8210bb1b5de6
-- title:
--   Every clipped-polytope vertex reaches the new cut face within the outer diameter budget
-- statement:
--   Let Q be a convex subset of R^d with padded vertex-edge diameter at most B, and let v be an extreme point of Q satisfying b<=<c,v>. Put P=Q intersect {x:<c,x><=b}. From EVERY extreme point u of P, an extreme point on the SPECIFIED cut plane <c,x>=b is reachable within B padded P-edge steps. There is no additive loss, factorization assumption, or low-rank assumption. A vertex of P lying strictly below the plane is proved to have been an extreme point of Q; if u is on the plane the constant walk suffices. For an original vertex below the plane, follow a B-step Q-walk to v until its first contact or crossing, retain the earlier edges, and clip that last edge. The outer walk need not be monotone. The conclusion does not select a particular cut-face vertex, does not concern an arbitrary old supporting face, and does not bound the entire diameter of P. No separate boundedness assumption is needed beyond the stated outer diameter and vertex hypotheses.
-- source:
--   Working derivation for the Polynomial Hirsch mission. jjoshua2/prove2me-work branch chatgpt/halfspace-routing; strict-cut vertex classification, exact segment clipping, and first-crossing proof. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.cut_face_access_of_outer_diameter
    (d B : ℕ) (Q : Set (EuclideanSpace ℝ (Fin d)))
    (hconv : Convex ℝ Q)
    (c : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (u : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}))
    (v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ Q) (hvge : b ≤ ⟪c, v⟫)
    (hD : DiamLE Q B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Q ∩ {x | ⟪c, x⟫ ≤ b}) ∧ ⟪c, z⟫ = b ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w B = z ∧
        ∀ j < B, w j = w (j + 1) ∨
          Adj (Q ∩ {x | ⟪c, x⟫ ≤ b}) (w j) (w (j + 1)) := by sorry
