-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_395ae7cf
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_395ae7cf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:25:31.087523+00:00
-- url     : https://prove2.me/theorems/2d86cd62-76d1-47b6-9827-5885da64d539
-- title:
--   Planar completion with the maximal edge count
-- statement:
--   Every graph with the specified planar drawing on at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_395ae7cf
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
