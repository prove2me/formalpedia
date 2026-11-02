-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:32.13444+00:00
-- url     : https://prove2.me/theorems/600971ac-633a-45eb-9e62-2fae1db8e0f7
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ (N : SimpleGraph V),
      (∀ u v, M.Adj u v → N.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      ∀ u v, N.Adj u v → M.Adj u v) :
    M.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
