-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_inclusion_maximal_drawing_561cc06e
-- name    : WilliamsonShmoys.planar_edge_count_of_inclusion_maximal_drawing_561cc06e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:24:29.972779+00:00
-- url     : https://prove2.me/theorems/09cd0f78-596e-4a94-9326-038b3be8d638
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_of_inclusion_maximal_drawing_561cc06e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset L.edgeSet M.edgeSet →
      L.edgeSet = M.edgeSet) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
