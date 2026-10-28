-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_extension_20261028
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_extension_20261028
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:45:41.738682+00:00
-- url     : https://prove2.me/theorems/c0e9c782-cfc4-40f7-9e9d-beb6072e80a8
-- title:
--   Extend a drawable graph to an edge-maximal drawable graph
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained, on the same vertex type, in a drawable graph that has no drawable proper supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_extension_20261028
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ G : SimpleGraph V, H.edgeSet ⊆ G.edgeSet →
        HasPlanarDrawingOn G → G.edgeSet ⊆ H.edgeSet := by sorry
