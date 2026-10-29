-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:07:37.100553+00:00
-- url     : https://prove2.me/theorems/9cf3c312-7626-4d52-80e3-dd84a4ffe5a7
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_lower_bound_4abbea4b_d91a_40b0_b03f_739e009c940e
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P) :
    3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
