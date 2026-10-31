-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:28:09.540841+00:00
-- url     : https://prove2.me/theorems/931a7134-e35c-41e8-a8b3-e1bad0c19dd8
-- title:
--   Planar triangulation extension with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n−6 edges. This isolates the planar augmentation and Euler-counting argument; the parent applies maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_extension__p2m_5b8e7ffd_8a89_4dff_8c54_ba70a4e1be67_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧ W.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
