-- Prove2me | Theorems.Thm_BookSixth_arc_last_exit_ball
-- name    : BookSixth.arc_last_exit_ball
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T15:28:36.126197+00:00
-- url     : https://prove2.me/theorems/17fe532e-7789-46d9-a2fa-a34d8353f2b5
-- title:
--   Last exit of a drawing edge from a vertex-centered ball
-- statement:
--   Let D be a good finite plane drawing, e one of its edges, and a and b its starting and finishing vertices. Use the distance of the drawing's plane, namely the supremum metric on the two real coordinates. For any radius r satisfying 0 < r < dist(b,a), there is a parameter t strictly between zero and one such that
--
--   $$d(D_e(t),a)=r.$$
--
--   For every parameter s > t the distance d(D_e(s),a) is strictly greater than r. This last-exit property permits trimming an edge near its initial vertex even when the edge visits the boundary repeatedly. It is a preparatory adapter for the polygonal-replacement route to the crossing-free edge bound, not an assertion of Euler's formula or an edge count.
-- source:
--   Derived from the extreme value and intermediate value theorems: Mathlib revision c5ea00351c28e24afc9f0f84379aa41082b1188f, Topology/Order/Compact.lean lines 158-160 (IsCompact.exists_isGreatest), https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Order/Compact.lean#L158-L160; Topology/Order/IntermediateValue.lean lines 552-554 (intermediate_value_Icc). Drawing definition: Prove2Me b1fcef2b-61fb-4326-bde6-cb6070d37c77. Intended parent obligation: b2255bec-31ff-4bf9-84b4-81705574eaac. This is a derived interface lemma, not a separately numbered book result.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.arc_last_exit_ball {N M : ℕ} (D : PlaneDrawing N M) (e : Fin M)
    (r : ℝ) (hr : 0 < r)
    (hrend : r < dist (D.vertex (D.right e)) (D.vertex (D.left e))) :
    ∃ t : EdgeParameter, 0 < t.val ∧ t.val < 1 ∧
      dist (D.arc e t) (D.vertex (D.left e)) = r ∧
      ∀ s : EdgeParameter, t.val < s.val →
        r < dist (D.arc e s) (D.vertex (D.left e)) := by sorry
