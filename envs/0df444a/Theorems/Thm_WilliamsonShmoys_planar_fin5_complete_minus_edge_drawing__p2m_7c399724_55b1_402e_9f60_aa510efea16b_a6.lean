-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_fin5_complete_minus_edge_drawing__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6
-- name    : WilliamsonShmoys.planar_fin5_complete_minus_edge_drawing__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T03:06:15.791548+00:00
-- url     : https://prove2.me/theorems/50cd08a9-fdd4-40bc-afbc-34df935162eb
-- title:
--   The five-vertex complete graph with one edge removed has a planar drawing
-- statement:
--   Construct a drawing for the graph on `Fin 5` that omits exactly the pair `{0,1}`. This supplies the planar premise of the reduction. Its concrete route is a triangular bipyramid drawing with piecewise-linear arcs, followed by checking the packaged arc conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_fin5_complete_minus_edge_drawing__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6 : WilliamsonShmoys.HasPlanarDrawingOn (SimpleGraph.fromRel (fun (x y : Fin 5) => x ≠ y ∧ ((x ≠ 0) ∨ (y ≠ 1)) ∧ ((x ≠ 1) ∨ (y ≠ 0)))) := by sorry
