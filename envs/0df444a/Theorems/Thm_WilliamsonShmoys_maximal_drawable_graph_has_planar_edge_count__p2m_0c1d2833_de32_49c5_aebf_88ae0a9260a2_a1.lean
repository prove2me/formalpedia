-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:46.377329+00:00
-- url     : https://prove2.me/theorems/7bdfbc7b-3903-44da-a815-425149078ac6
-- title:
--   Maximal drawable graphs have the planar edge count
-- statement:
--   A graph on at least three vertices that has a crossing-free drawing and is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges. The vertex-count condition is retained to cover the range where the planar edge formula applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_has_planar_edge_count__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
