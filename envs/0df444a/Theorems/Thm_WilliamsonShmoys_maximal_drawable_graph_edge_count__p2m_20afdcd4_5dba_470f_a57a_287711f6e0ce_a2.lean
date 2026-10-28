-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:13:25.99322+00:00
-- url     : https://prove2.me/theorems/c4dc32d3-4855-4c98-90fe-4846f7b25dee
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : forall N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N -> M <= N -> N = M)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
