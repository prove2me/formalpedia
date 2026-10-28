-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists_v3
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:55:40.413051+00:00
-- url     : https://prove2.me/theorems/55c57bb9-f8db-487f-b94e-208e0810468d
-- title:
--   A finite maximal drawable supergraph exists
-- statement:
--   Any drawable graph on a finite vertex type is contained in a drawable graph maximal under drawable supergraph inclusion, with at least as many edges. This isolates the finite maximization step from the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ H' : SimpleGraph V,
        H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H := by sorry
