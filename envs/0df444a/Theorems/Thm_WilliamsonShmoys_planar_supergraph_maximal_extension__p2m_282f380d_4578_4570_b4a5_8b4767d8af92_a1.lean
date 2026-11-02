-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:12:30.72398+00:00
-- url     : https://prove2.me/theorems/1cc8a528-581b-4730-9b06-c7661493ce8a
-- title:
--   Every drawable finite graph has an inclusion-maximal drawable supergraph
-- statement:
--   For any drawable simple graph on a finite linearly ordered vertex type, there is a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension__p2m_282f380d_4578_4570_b4a5_8b4767d8af92_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
