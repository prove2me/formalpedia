-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:46:40.68128+00:00
-- url     : https://prove2.me/theorems/748c3a8f-413b-4adb-bf96-a7fe063f95f4
-- title:
--   Edge bound for an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable finite simple graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
