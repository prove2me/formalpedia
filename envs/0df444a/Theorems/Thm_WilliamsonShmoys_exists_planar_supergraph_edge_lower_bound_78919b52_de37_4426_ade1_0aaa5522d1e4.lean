-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:52:11.197855+00:00
-- url     : https://prove2.me/theorems/b148b87e-dff5-44f5-a9e8-29914bba0e7e
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every crossing-free drawing on at least three vertices has a crossing-free planar supergraph on the same vertices with at least 3|V|−6 edges. This removes the geometric augmentation and planar edge-count argument from the parent; it follows by extending to a maximal planar embedding, triangulating its faces, and applying Euler’s formula, with the three-vertex case handled by the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound_78919b52_de37_4426_ade1_0aaa5522d1e4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
