-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_count_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:15:16.104997+00:00
-- url     : https://prove2.me/theorems/878a8c99-ad07-493a-8992-477d24f14346
-- title:
--   Maximal drawable supergraph on the same vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex type has a drawable supergraph on the same vertex type that is maximal under inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_count_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    ∃ L : SimpleGraph V, M ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L := by sorry
