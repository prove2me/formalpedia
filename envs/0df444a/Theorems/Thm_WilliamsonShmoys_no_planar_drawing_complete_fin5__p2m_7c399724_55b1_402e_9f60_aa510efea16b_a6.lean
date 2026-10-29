-- Prove2me | Theorems.Thm_WilliamsonShmoys_no_planar_drawing_complete_fin5__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6
-- name    : WilliamsonShmoys.no_planar_drawing_complete_fin5__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T03:06:20.621794+00:00
-- url     : https://prove2.me/theorems/873f9043-20c8-468d-8403-d872e3d46441
-- title:
--   The complete graph on five vertices has no planar drawing
-- statement:
--   Show that any graph on `Fin 5` containing every distinct pair cannot satisfy the drawing predicate. This rules out the supergraph produced by the augmentation claim. A proof route derives the planar simple-graph edge bound from the arc conditions and contradicts it with the ten edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.no_planar_drawing_complete_fin5__p2m_7c399724_55b1_402e_9f60_aa510efea16b_a6 (M : SimpleGraph (Fin 5)) (hM : ∀ x y : Fin 5, x ≠ y → M.Adj x y) : ¬ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
