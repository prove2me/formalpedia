-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:04:20.674469+00:00
-- url     : https://prove2.me/theorems/a3d46af7-d8d1-44e5-ae3d-980c06c923f9
-- title:
--   Lower bound from maximal drawable supergraphs
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs has at least 3V−6 edges. The proof route is to extract a plane embedding, use maximality to rule out faces with drawable diagonals and establish triangulation, then count incidences using Euler's formula. The boundary case of three vertices is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_1112e69e_48a4_4643_92d8_b48cd86b06af_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    3 * C.supp.ncard ≤ M.edgeSet.ncard + 6 := by sorry
