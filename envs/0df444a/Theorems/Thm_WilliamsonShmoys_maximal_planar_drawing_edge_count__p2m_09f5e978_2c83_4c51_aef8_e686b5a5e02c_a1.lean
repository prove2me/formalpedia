-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:56.735522+00:00
-- url     : https://prove2.me/theorems/09a7ea27-8f3a-49eb-bec8-9d191564106c
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   A graph on at least three vertices that is maximal among planar supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_09f5e978_2c83_4c51_aef8_e686b5a5e02c_a1 {V : Type} [Fintype V] [LinearOrder V] (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J) : 3 * Fintype.card V - 6 = J.edgeSet.ncard := by sorry
