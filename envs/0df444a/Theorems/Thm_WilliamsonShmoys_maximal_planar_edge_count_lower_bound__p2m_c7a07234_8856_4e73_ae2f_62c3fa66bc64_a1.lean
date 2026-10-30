-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:39:51.253502+00:00
-- url     : https://prove2.me/theorems/295c0ef8-5d8f-41a3-8c9f-ccd6cdcf9c48
-- title:
--   Maximal planar graphs attain the Euler edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is edge-maximal among its drawable supergraphs has at least 3|V|−6 edges. This is the maximality/triangulation half of the target. The three-vertex boundary gives a zero lower bound, consistent with a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c7a07234_8856_4e73_ae2f_62c3fa66bc64_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet.ncard ≤ N.edgeSet.ncard) :
    3 * Fintype.card V - 6 ≤ N.edgeSet.ncard := by sorry
