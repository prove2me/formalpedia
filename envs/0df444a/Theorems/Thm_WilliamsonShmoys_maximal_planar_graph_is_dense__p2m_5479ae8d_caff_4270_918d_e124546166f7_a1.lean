-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:34:08.847312+00:00
-- url     : https://prove2.me/theorems/48acce6a-8f33-48c6-a9d8-ff0d2e5ac6c0
-- title:
--   Maximal planar graphs have at least 3n−6 edges
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a finite vertex set of size at least three has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_graph_is_dense__p2m_5479ae8d_caff_4270_918d_e124546166f7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ M : SimpleGraph V, N ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ N) :
    3 * Fintype.card V ≤ N.edgeSet.ncard + 6 := by sorry
