-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:03:21.223724+00:00
-- url     : https://prove2.me/theorems/6040d514-90bd-48aa-80b3-92cc416e4fa5
-- title:
--   Finite maximal planar supergraph on the same vertices
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a planar supergraph on that same vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_cd050b01_9a07_4b9b_9132_918bb6a60ec5
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
