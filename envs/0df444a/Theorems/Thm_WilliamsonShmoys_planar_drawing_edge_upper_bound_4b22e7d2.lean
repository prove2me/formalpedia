-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound_4b22e7d2
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound_4b22e7d2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:04:35.313229+00:00
-- url     : https://prove2.me/theorems/f7aad79a-9ceb-4052-a042-586a283ab4a2
-- title:
--   Edge upper bound for a planar drawing
-- statement:
--   Every graph with the supplied crossing-free drawing and at least three vertices has at most \(3|V|-6\) edges. The independent proof route is Euler’s formula and face-boundary counting, with disconnected components handled explicitly or by planar augmentation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound_4b22e7d2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
