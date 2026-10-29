-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
-- name    : WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:28:18.126455+00:00
-- url     : https://prove2.me/theorems/30b95b10-9312-4a58-bfd2-1ede6bd3cff8
-- title:
--   Drawable graphs admit a triangulated planar extension
-- statement:
--   Every drawable simple graph on at least three vertices can be extended, on the same vertex set, to a drawable graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_augmentation_exact_edge_count_3e869d1e_d221_44f3_8f2b_71d5fc6eb8db
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
