-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:15.984029+00:00
-- url     : https://prove2.me/theorems/4cd8dc85-f1ac-41e1-bc75-323e85ca2348
-- title:
--   Maximal drawable graph edge count lower bound
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on a fixed vertex set of size at least three has at least 3n−6 edges. The proof route is to use maximality to obtain connectedness and triangular faces, then apply Euler’s formula; the n=3 case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_0d663055_40d3_4575_b5af_11ff2bc59459_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
