-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- name    : WilliamsonShmoys.planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:09:51.897983+00:00
-- url     : https://prove2.me/theorems/7c755e17-c172-495f-92b3-57f52b2775d5
-- title:
--   Drawable graphs extend to the planar edge count
-- statement:
--   Any finite drawable simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This covers disconnected inputs; the three-vertex case yields the triangle. The geometric augmentation and Euler counting are the core work assigned to this child. The parent applies maximality to the resulting supergraph and substitutes its edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_edge_count_extension_a1d336b1_f975_4a54_a7fc_c4dfef1e43c2
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hXdraw : WilliamsonShmoys.HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧
      WilliamsonShmoys.HasPlanarDrawingOn Y ∧
      3 * Fintype.card V = Y.edgeSet.ncard + 6 := by sorry
