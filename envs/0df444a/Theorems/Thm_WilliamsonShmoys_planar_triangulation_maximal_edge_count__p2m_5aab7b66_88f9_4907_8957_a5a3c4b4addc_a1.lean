-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- name    : WilliamsonShmoys.planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:36.488174+00:00
-- url     : https://prove2.me/theorems/996f417d-299f-4de3-98ff-54d66e679a8a
-- title:
--   Edge count of a maximum-edge planar graph
-- statement:
--   A drawable simple graph on at least three vertices whose drawable supergraphs cannot have more edges has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_maximal_edge_count__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hU : WilliamsonShmoys.HasPlanarDrawingOn U) (hV : 3 ≤ Fintype.card V) (hmax : ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W.edgeSet.ncard ≤ U.edgeSet.ncard) : U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
