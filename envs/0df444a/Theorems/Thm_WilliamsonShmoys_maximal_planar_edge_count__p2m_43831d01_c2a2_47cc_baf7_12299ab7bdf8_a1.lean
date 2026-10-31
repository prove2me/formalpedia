-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:21:25.518901+00:00
-- url     : https://prove2.me/theorems/c9a3871e-5cc1-4338-ae1f-e59bec6b3362
-- title:
--   Count the edges of an edge-maximal planar graph
-- statement:
--   A planar graph on at least three vertices that is maximal among planar graphs on the same vertex set has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_43831d01_c2a2_47cc_baf7_12299ab7bdf8_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) (hmax : ∀ J : SimpleGraph V, H <= J → HasPlanarDrawingOn J → J <= H) : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
