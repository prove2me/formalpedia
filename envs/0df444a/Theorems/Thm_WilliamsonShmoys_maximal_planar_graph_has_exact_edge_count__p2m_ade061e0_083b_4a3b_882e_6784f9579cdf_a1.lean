-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:15:19.54215+00:00
-- url     : https://prove2.me/theorems/2f707832-942f-4ae9-9944-7f0d941152ce
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable simple graph on at least three vertices with no drawable strict supergraph has exactly three times its vertex count minus six edges. The proof uses triangulation of maximal planar drawings and Euler’s formula; the hypothesis includes the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_has_exact_edge_count__p2m_ade061e0_083b_4a3b_882e_6784f9579cdf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
