-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:37.785198+00:00
-- url     : https://prove2.me/theorems/c433045e-87b9-4ae4-bc06-deb72cf5a3b9
-- title:
--   Extend a drawable graph to an edge maximal drawable graph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under drawable supergraph inclusion. The proof route is finite maximization: the set of simple graphs on a finite vertex type is finite, the candidate family is nonempty because it contains the input graph, and a candidate with maximum edge count is inclusion maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1fc721c4_d4d8_4a3d_8e5b_8d3e1462bbc6_a1 {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hS : HasPlanarDrawingOn S) : ∃ T : SimpleGraph V, S ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U = T := by sorry
