-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce_subset
-- name    : WilliamsonShmoys.planar_drawing_induce_subset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:41:45.877144+00:00
-- url     : https://prove2.me/theorems/2866aee3-fa50-474f-a792-515668ef26cf
-- title:
--   Restrict a planar drawing to an induced subset
-- statement:
--   Restrict the vertex placement and edge arcs of a crossing-free drawing on Fin n to the vertices in S. The induced subtype order preserves the edge orientation conditions, and injectivity and noncrossing pass to the restricted arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_induce_subset
    {n : Nat} (G : SimpleGraph (Fin n))
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (S : Set (Fin n)) [Fintype S] :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce S) := by sorry
