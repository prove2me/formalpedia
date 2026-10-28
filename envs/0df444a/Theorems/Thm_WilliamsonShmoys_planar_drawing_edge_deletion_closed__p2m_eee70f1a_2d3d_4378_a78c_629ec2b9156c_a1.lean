-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:19:55.99467+00:00
-- url     : https://prove2.me/theorems/ea226d6c-bcfa-4e35-b5a1-53b49ed2687f
-- title:
--   Planar drawings persist after edge deletion
-- statement:
--   Deleting edges from a graph with a drawing on the same vertices preserves the drawing property. The proof reuses the positions and arcs for F; all drawing obligations for G apply to a subset of F's edges. This removes the hereditary-property obligation from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_deletion_closed__p2m_eee70f1a_2d3d_4378_a78c_629ec2b9156c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G F : SimpleGraph V)
    (hGF : G.edgeSet ⊆ F.edgeSet)
    (hF : WilliamsonShmoys.HasPlanarDrawingOn F) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
