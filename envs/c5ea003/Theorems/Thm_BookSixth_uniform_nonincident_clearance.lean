-- Prove2me | Theorems.Thm_BookSixth_uniform_nonincident_clearance
-- name    : BookSixth.uniform_nonincident_clearance
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T16:36:34.372036+00:00
-- url     : https://prove2.me/theorems/2cf49d97-eb36-4f8c-9b3e-5c08490c6145
-- title:
--   Uniform clearance of vertices from nonincident drawing edges
-- statement:
--   Let D be a finite good plane drawing with N labeled vertices and M labeled edges. There is a single radius r > 0 such that, for every vertex v and every edge e not incident to v, every point of the edge is farther than r from v:
--
--   $$d(D_e(t),D(v))>r.$$
--
--   This holds for every parameter t in the closed unit interval. The distance is the supremum metric on the two real coordinates. Empty drawings and drawings with no nonincident vertex-edge pairs are included. This uniform separation is a preparatory fact for choosing vertex neighborhoods during polygonal replacement of a drawing; it asserts no planar edge count or Euler equality.
-- source:
--   Derived compactness adapter for BookSixth.crossing_free_subset_edge_bound (b2255bec-31ff-4bf9-84b4-81705574eaac), using the canonical drawing definition b1fcef2b-61fb-4326-bde6-cb6070d37c77 and the extreme value theorem IsCompact.exists_forall_le', Mathlib revision c5ea00351c28e24afc9f0f84379aa41082b1188f, Topology/Order/Compact.lean lines 238-245: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Topology/Order/Compact.lean#L238-L245. This is a derived lemma, not a separately numbered book theorem.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.uniform_nonincident_clearance {N M : ℕ} (D : PlaneDrawing N M) :
    ∃ r : ℝ, 0 < r ∧ ∀ (v : Fin N) (e : Fin M),
      D.left e ≠ v → D.right e ≠ v → ∀ t : EdgeParameter,
        r < dist (D.arc e t) (D.vertex v) := by sorry
