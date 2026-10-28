-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_bb1e381f_3bfa_43e8_873d_4da72a56878c_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_bb1e381f_3bfa_43e8_873d_4da72a56878c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:25:16.3257+00:00
-- url     : https://prove2.me/theorems/117a5bc6-0e8c-496f-accb-a7c904e7cb02
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A maximally drawable simple graph with at least three vertices has exactly three times its vertex count minus six edges. This isolates the planar extremal-edge argument; the parent theorem then follows by arithmetic from this identity and Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_bb1e381f_3bfa_43e8_873d_4da72a56878c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
