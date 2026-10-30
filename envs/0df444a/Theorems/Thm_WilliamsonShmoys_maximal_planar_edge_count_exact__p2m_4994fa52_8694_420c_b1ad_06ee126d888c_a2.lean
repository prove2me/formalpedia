-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:41.085619+00:00
-- url     : https://prove2.me/theorems/247cb426-33af-4a81-8384-dca9c0e8b445
-- title:
--   Exact edge count for an inclusion-maximal planar graph
-- statement:
--   A drawable graph that is maximal under inclusion among drawable graphs on the same finite ordered vertex type has exactly $3|V|-6$ edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_exact__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ (J : SimpleGraph V),
      G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ G)
    (hcard : 3 ≤ Fintype.card V) :
    G.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
