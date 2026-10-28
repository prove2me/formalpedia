-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_map_exists
-- name    : WilliamsonShmoys.maximal_planar_map_exists
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:50:14.886581+00:00
-- url     : https://prove2.me/theorems/5c98657a-01dd-48af-88dd-08bf5f0cfcaf
-- title:
--   Triangular map for a maximal planar drawing
-- statement:
--   A drawing-maximal simple planar graph on at least three vertices has a finite oriented triangular map as defined in the attached structure. The map existence follows by extracting a spherical embedding from the drawing and using maximality to ensure triangular faces; this step does not assert the face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_map_exists
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap H (Fin m)) := by sorry
