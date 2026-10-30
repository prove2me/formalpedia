-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:13.968865+00:00
-- url     : https://prove2.me/theorems/d4833247-a107-430f-bfde-1b2cd697853a
-- title:
--   Maximal drawing reaches the planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges. Maximality forces triangular faces, giving the reverse bound from Euler’s formula and edge-face incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H' →
      H'.edgeSet = H.edgeSet) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
