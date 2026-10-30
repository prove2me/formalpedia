-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- name    : WilliamsonShmoys.planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:20:37.650738+00:00
-- url     : https://prove2.me/theorems/326c8e6c-2fee-4ab9-b71e-76b7c3f2eeb5
-- title:
--   Strict planar extension below the triangulation bound
-- statement:
--   If a drawable graph on at least three vertices has fewer than three times its vertex count minus six edges, it has a drawable strict supergraph on the same vertices. A proof route is to augment its drawing to a triangulation while retaining all vertices; Euler’s formula gives the completed graph the full edge count, so the strict-extension conclusion follows. This removes the lower-bound half of the target; the remaining core is formalizing planar augmentation and its preservation of the supplied drawing predicate, including disconnected drawings and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_strict_extension_below_bound__p2m_88a3bf29_1582_4605_aca9_2743ecb4531b_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ M : SimpleGraph V, G ≤ M ∧ M ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn M := by sorry
