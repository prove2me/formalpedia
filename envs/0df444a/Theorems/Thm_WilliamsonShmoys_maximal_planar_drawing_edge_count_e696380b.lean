-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e696380b
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_e696380b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:51:53.913999+00:00
-- url     : https://prove2.me/theorems/181dc787-c5f0-46e8-8e1b-bea7950667c2
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_e696380b
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V,
      K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
