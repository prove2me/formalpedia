-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:08.670145+00:00
-- url     : https://prove2.me/theorems/d410bfc9-f026-41fa-b924-9663ab8f4a24
-- title:
--   An inclusion-maximal drawable graph has the planar maximal edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The edge-count argument uses triangulation of a maximal planar embedding and Euler’s formula, including the three-vertex triangle case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b8d35c99_ccc1_4cae_8065_458ad4737ca1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
