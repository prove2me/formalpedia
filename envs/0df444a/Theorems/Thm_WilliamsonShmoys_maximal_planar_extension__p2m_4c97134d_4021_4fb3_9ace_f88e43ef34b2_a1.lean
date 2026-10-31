-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:21:10.148108+00:00
-- url     : https://prove2.me/theorems/a8fe5744-6105-486c-9111-1eda044d246f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that has no proper drawable supergraph on the same vertex set. Finiteness of the possible supergraphs gives an independent proof route by maximizing the number of edges while retaining a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_4c97134d_4021_4fb3_9ace_f88e43ef34b2_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
