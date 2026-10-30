-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:37.3866+00:00
-- url     : https://prove2.me/theorems/3be79666-71db-45ff-88b4-e34036e94e74
-- title:
--   An inclusion-maximal drawable graph has the triangulation edge count
-- statement:
--   If a finite drawable simple graph is maximal among drawable supergraphs on the same vertex type and has at least three vertices, then its number of edges is `3|V|−6`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_8e19dc79_980c_4b90_a9e5_d9bf409450af_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
