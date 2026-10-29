-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- name    : WilliamsonShmoys.planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:27:40.149247+00:00
-- url     : https://prove2.me/theorems/f6fbb2eb-cab6-4ebc-b0c8-9e00fa476533
-- title:
--   Extension of a drawable graph to a triangulated planar graph
-- statement:
--   Any drawable finite simple graph on at least three vertices is a subgraph of a drawable graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_triangulation__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ M : SimpleGraph V, G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
