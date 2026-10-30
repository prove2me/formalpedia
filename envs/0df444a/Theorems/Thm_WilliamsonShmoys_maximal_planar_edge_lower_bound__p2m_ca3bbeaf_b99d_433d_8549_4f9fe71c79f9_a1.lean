-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:35:16.127789+00:00
-- url     : https://prove2.me/theorems/9ec06c2a-4897-4f0a-9340-6489b642dcd9
-- title:
--   Maximal drawable graphs attain the Euler edge bound
-- statement:
--   A drawable graph that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges when it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_ca3bbeaf_b99d_433d_8549_4f9fe71c79f9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by sorry
