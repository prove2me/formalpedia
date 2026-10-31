-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:44:06.924447+00:00
-- url     : https://prove2.me/theorems/8c2c228b-ec99-4f65-be1c-c56ad3f2b418
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_supergraph__p2m_34be30da_42b8_40a1_89e9_f0ba3aa7e7d4_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
