-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:23:35.445828+00:00
-- url     : https://prove2.me/theorems/bc657f31-eaae-4f57-ab42-14b02319f13d
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has exactly 3|V|−6 edges. This isolates the planar topology and Euler-formula argument needed after the finite maximal-supergraph choice. The lower bound on the number of vertices is necessary for the stated edge-count formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_ef0860d4_4cfe_4ed1_9f37_9a24872db6ea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ W : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn W → U ≤ W → W ≤ U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
