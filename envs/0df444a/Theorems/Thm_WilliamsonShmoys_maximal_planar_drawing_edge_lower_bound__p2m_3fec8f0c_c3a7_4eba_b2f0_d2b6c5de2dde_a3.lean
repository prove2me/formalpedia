-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T22:31:45.370065+00:00
-- url     : https://prove2.me/theorems/3a830fa8-5714-4871-98bd-724059b55494
-- title:
--   Maximal drawable graphs reach the planar edge bound
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_3fec8f0c_c3a7_4eba_b2f0_d2b6c5de2dde_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
