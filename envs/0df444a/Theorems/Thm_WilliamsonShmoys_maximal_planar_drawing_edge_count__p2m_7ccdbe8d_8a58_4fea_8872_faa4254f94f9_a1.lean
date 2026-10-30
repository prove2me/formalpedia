-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:29:46.019967+00:00
-- url     : https://prove2.me/theorems/ac6eb2e4-2427-46c2-b7cd-156017af8bc0
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable simple graph on at least three vertices whose edge count is maximal among its drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. This isolates the plane-topology and Euler-counting argument from the finite selection of a maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ J : SimpleGraph V, G ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet.ncard ≤ G.edgeSet.ncard) : G.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
