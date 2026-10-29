-- Prove2me | Theorems.Thm_WilliamsonShmoys_hasPlanarDrawingOn_connectedComponent__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- name    : WilliamsonShmoys.hasPlanarDrawingOn_connectedComponent__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:23:38.454448+00:00
-- url     : https://prove2.me/theorems/a22da3e1-2d0c-4cc1-bbc7-316fd89bf161
-- title:
--   Restricting a planar drawing to a connected component
-- statement:
--   Restricting the vertex placement and edge arcs to a connected component preserves the drawing conditions. The explicit finite instance covers the component’s subtype of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.hasPlanarDrawingOn_connectedComponent__p2m_e46e8dd0_1680_4d93_a7d5_10e0bd7d8348_a4 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (C : G.ConnectedComponent) [Fintype {v : V // v ∈ C.supp}] : WilliamsonShmoys.HasPlanarDrawingOn C.toSimpleGraph := by sorry
