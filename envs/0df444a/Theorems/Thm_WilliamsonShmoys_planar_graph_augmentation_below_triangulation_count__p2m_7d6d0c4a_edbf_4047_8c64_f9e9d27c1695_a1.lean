-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
-- name    : WilliamsonShmoys.planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:57:37.579929+00:00
-- url     : https://prove2.me/theorems/dedf5137-e1df-470f-a755-e725cf271f52
-- title:
--   Planar edge augmentation below the triangulation count
-- statement:
--   If a drawable finite simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a proper drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_augmentation_below_triangulation_count__p2m_7d6d0c4a_edbf_4047_8c64_f9e9d27c1695_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) (hSmall : G.edgeSet.ncard < 3 * Fintype.card V - 6) : ∃ K : SimpleGraph V, G ≤ K ∧ K ≠ G ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
