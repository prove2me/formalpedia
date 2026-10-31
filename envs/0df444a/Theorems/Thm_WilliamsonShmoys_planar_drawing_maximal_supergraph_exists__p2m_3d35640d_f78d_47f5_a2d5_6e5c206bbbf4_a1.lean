-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:35:29.003985+00:00
-- url     : https://prove2.me/theorems/6b2b37c2-a3cd-4c92-9c59-19c1512cb06f
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite graph with a planar drawing has a drawable supergraph on the same vertices that is maximal among drawable supergraphs; the extension contains at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_3d35640d_f78d_47f5_a2d5_6e5c206bbbf4_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
