-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_supergraph_same_vertex_completion_7e0405ab
-- name    : WilliamsonShmoys.finite_maximal_planar_supergraph_same_vertex_completion_7e0405ab
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:52:53.943337+00:00
-- url     : https://prove2.me/theorems/32b54d0d-b0b8-436d-85e7-e4fa5d8b919e
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Any drawable finite graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs and has at least as many edges as the original. No lower bound on the vertex count is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_supergraph_same_vertex_completion_7e0405ab {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard ∧ ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by sorry
