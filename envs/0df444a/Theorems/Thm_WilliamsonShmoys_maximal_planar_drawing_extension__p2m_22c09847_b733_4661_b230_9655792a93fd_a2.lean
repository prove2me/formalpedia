-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:43:30.271207+00:00
-- url     : https://prove2.me/theorems/caeb5dd4-5fd2-4c55-bf82-08893d3a46eb
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every finite graph with a drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_extension__p2m_22c09847_b733_4661_b230_9655792a93fd_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
