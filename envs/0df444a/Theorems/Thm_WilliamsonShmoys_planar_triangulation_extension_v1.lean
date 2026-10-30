-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_v1
-- name    : WilliamsonShmoys.planar_triangulation_extension_v1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:55:48.767846+00:00
-- url     : https://prove2.me/theorems/219c2427-f0ca-410a-8cab-2194ee3f8b9c
-- title:
--   Planar triangulation extension on the same vertex set
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of at least three vertices is a subgraph of a planar graph on the same vertex type with exactly 3|V|−6 edges. A proof route is to extend a planar drawing to a triangulation by inserting noncrossing edges, then use Euler’s formula and count each face boundary edge twice. The inserted arcs must satisfy the target’s endpoint-only intersection conditions, and the argument must handle disconnected drawings and boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_v1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
