-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- name    : WilliamsonShmoys.planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:42:13.522572+00:00
-- url     : https://prove2.me/theorems/5ee69774-33ce-43a4-80f8-d6fa2fe5a765
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Every finite simple graph with a drawing satisfying HasPlanarDrawingOn and at least three vertices is a subgraph of a drawable triangulated graph on the same vertex set, whose edge count is exactly 3n − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_completion_d42c8f91_ac47_4320_bc80_c3d77a1995cc
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
