-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_extension_for_edge_count_bound
-- name    : WilliamsonShmoys.planar_drawing_triangulated_extension_for_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T15:59:19.166563+00:00
-- url     : https://prove2.me/theorems/bcc8c98b-d4c1-462d-9be8-fb6e4c745d1d
-- title:
--   Triangulated drawable extension with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices extends, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges. At three vertices the extension may be the triangle. A proof route is to complete the drawing to a connected triangulation, then derive the edge count from Euler's formula and the fact that each face has three sides. The geometric augmentation and its connection to Euler's formula remain the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_extension_for_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, M ≤ L ∧ HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
