-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_dense_extension
-- name    : WilliamsonShmoys.planar_drawing_has_dense_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:52:49.932717+00:00
-- url     : https://prove2.me/theorems/09ada26b-2cb5-41e6-8ec2-c20f998f04ba
-- title:
--   A drawable graph has a dense drawable extension
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices with at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_dense_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ W : SimpleGraph V, G.edgeSet ⊆ W.edgeSet ∧
      HasPlanarDrawingOn W ∧
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by sorry
