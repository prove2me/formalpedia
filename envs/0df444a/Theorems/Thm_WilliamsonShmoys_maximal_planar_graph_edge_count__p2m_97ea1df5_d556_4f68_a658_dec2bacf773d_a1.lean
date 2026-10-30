-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:22.51118+00:00
-- url     : https://prove2.me/theorems/d5e355eb-db93-4745-85ca-eb9a9a9b0ce3
-- title:
--   Maximal drawable graphs have the triangulation edge count
-- statement:
--   A finite drawable simple graph on at least three vertices that is maximal among drawable supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_97ea1df5_d556_4f68_a658_dec2bacf773d_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) : K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
