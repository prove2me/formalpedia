-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:13.75702+00:00
-- url     : https://prove2.me/theorems/9871e0da-e68a-4b12-838d-3e260e2dafe6
-- title:
--   Planar edge upper bound for a maximal drawing
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex set has at most 3|V|−6 edges. This is the Euler and face-incidence upper-bound direction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_upper_bound__p2m_8980508c_eade_47a8_94c5_e0127b6a85f8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H' →
      H'.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
