-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_maximal_planar_drawing_v2
-- name    : WilliamsonShmoys.edge_bound_of_maximal_planar_drawing_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:10:51.645675+00:00
-- url     : https://prove2.me/theorems/7cd50ea2-7bd9-44f6-aada-9741465deea3
-- title:
--   Maximal drawable graphs meet the planar edge bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has at least 3|V|−6 edges. The core argument uses maximality to obtain a triangulated planar embedding, then Euler’s formula and the count of edge incidences on face boundaries. The three-vertex boundary case satisfies the same bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_bound_of_maximal_planar_drawing_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hPdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hPmax : ∀ Q : SimpleGraph V,
      P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
