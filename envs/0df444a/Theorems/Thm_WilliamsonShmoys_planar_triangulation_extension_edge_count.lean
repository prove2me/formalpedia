-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:02:49.729621+00:00
-- url     : https://prove2.me/theorems/16ffb502-93fc-49b2-aaba-3b0bbd9854a4
-- title:
--   Planar graph extension to a triangulation
-- statement:
--   Any finite simple graph with a crossing-free drawing and at least three vertices can be extended, using the same vertex set, to a planar triangulation with exactly 3|V|−6 edges. This extension is the substantial topological step: add drawable nonedges until the embedding is maximal, prove it is connected and all faces are triangles, and use Euler’s formula. For |V|=3 the result is the triangle case. The parent invokes maximality to show the original graph equals this extension, yielding the lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
