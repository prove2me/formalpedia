-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:42.753102+00:00
-- url     : https://prove2.me/theorems/c5b64a3b-d324-45a7-86e6-d358f6728245
-- title:
--   Maximality forces the matching planar edge lower bound
-- statement:
--   If a drawable graph is maximal among drawable supergraphs on the same vertex type, and there are at least three vertices, it has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_maximal_lower_bound__p2m_247cb426_33af_4a81_8384_dca9c0e8b445_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ (J : SimpleGraph V),
      G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ G)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ G.edgeFinset.card := by
  sorry
