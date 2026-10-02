-- Prove2me | Theorems.Thm_BookSixth_arc_small_radius_last_exit
-- name    : BookSixth.arc_small_radius_last_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T16:46:02.076429+00:00
-- url     : https://prove2.me/theorems/d7b71143-aee4-436c-a1cf-1ece84dafc8d
-- title:
--   Small-radius last exits precede any positive parameter cutoff
-- statement:
--   Let D be a good finite plane drawing, e one of its edges, and a a parameter in the closed unit interval with a > 0. There exists R > 0 such that every radius r with 0 < r < R has a last boundary contact at a parameter t satisfying 0 < t < a and
--
--   $$d(D_e(t),D_e(0))=r.$$
--
--   At every later parameter s > t the distance from the initial vertex is strictly greater than r. Distances use the supremum metric on the two real coordinates. This localizes endpoint trimming before a prescribed cutoff; it assumes no differentiability and does not assert a planar edge count.
-- source:
--   Derived localization of BookSixth.arc_last_exit_ball (17fe532e-7789-46d9-a2fa-a34d8353f2b5), using injectivity of the canonical arc and IsCompact.exists_forall_le', Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, Topology/Order/Compact.lean lines 238-245: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Order/Compact.lean#L238-L245. Preparatory obligation for polygonal replacement in BookSixth.crossing_free_subset_edge_bound (b2255bec-31ff-4bf9-84b4-81705574eaac), not a separately numbered book theorem.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.arc_small_radius_last_exit {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    (a : EdgeParameter) (ha : 0 < a.val) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      ∃ t : EdgeParameter, 0 < t.val ∧ t.val < a.val ∧
        dist (D.arc e t) (D.vertex (D.left e)) = r ∧
        ∀ s : EdgeParameter, t.val < s.val →
          r < dist (D.arc e s) (D.vertex (D.left e)) := by sorry
