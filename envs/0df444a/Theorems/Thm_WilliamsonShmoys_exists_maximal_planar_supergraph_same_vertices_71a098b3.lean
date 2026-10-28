-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_71a098b3
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_71a098b3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:51:43.307005+00:00
-- url     : https://prove2.me/theorems/e614fef5-8c52-4b76-8053-5c1615b26179
-- title:
--   A drawable graph has a maximal drawable supergraph on the same vertices
-- statement:
--   Every finite drawable simple graph has an inclusion-maximal drawable simple supergraph on the same vertex set. The proof can maximize edge count over the finite set of supergraphs that admit a drawing; it may choose a new drawing for the resulting graph, including when the original graph is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_71a098b3 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) : ∃ K : SimpleGraph V, J ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
