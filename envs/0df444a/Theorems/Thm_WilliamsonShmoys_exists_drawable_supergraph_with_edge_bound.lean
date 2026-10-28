-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_supergraph_with_edge_bound
-- name    : WilliamsonShmoys.exists_drawable_supergraph_with_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:38:44.741973+00:00
-- url     : https://prove2.me/theorems/b1fff909-3724-4412-b571-7f014957ce50
-- title:
--   Drawable supergraph with planar edge lower bound
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges. The three-vertex boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_supergraph_with_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
