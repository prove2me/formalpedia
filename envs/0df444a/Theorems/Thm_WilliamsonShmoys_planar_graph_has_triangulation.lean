-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulation
-- name    : WilliamsonShmoys.planar_graph_has_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:00:28.076595+00:00
-- url     : https://prove2.me/theorems/6e15fe35-948b-4936-bdf8-fbdd63dba4ea
-- title:
--   Completion of a drawable graph to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set whose edge count is 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 <= Fintype.card V) :
    ∃ M : SimpleGraph V, G <= M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
