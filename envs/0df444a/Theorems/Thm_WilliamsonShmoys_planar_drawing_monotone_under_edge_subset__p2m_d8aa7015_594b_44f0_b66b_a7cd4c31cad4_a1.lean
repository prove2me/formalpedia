-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- name    : WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:34:17.599648+00:00
-- url     : https://prove2.me/theorems/e693e4fe-61ca-4588-ad00-faffd59c8669
-- title:
--   Planar drawings are preserved when edges are removed
-- statement:
--   If G is a subgraph of H and H has a crossing-free drawing, then G has one, witnessed by the same vertex positions and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_monotone_under_edge_subset__p2m_d8aa7015_594b_44f0_b66b_a7cd4c31cad4_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : Set.Subset G.edgeSet H.edgeSet) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by
  sorry
