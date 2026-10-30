-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:28:26.456641+00:00
-- url     : https://prove2.me/theorems/7871e1d9-1c06-462f-bc77-343c5987d399
-- title:
--   Maximal planar completion with the full edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges. The child isolates the planar augmentation and Euler-count argument; the parent uses the strict edge bound to show the completion is a strict extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_completion_edge_count__p2m_326c8e6c_2fee_4ab9_b71e_76b7c3f2eeb5_a1 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
