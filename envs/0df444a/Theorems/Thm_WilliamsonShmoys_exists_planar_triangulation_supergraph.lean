-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:08:55.684009+00:00
-- url     : https://prove2.me/theorems/3e41a808-4fb6-4a29-a7b9-7bf6f3b8d966
-- title:
--   A planar graph extends to a triangulation on the same vertices
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    ∃ H : SimpleGraph V,
      T ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
