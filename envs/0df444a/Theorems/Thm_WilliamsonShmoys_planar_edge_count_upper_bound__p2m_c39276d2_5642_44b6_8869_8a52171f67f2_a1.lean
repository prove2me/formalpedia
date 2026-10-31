-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:15.852632+00:00
-- url     : https://prove2.me/theorems/cb18c991-2437-4ca3-b7e7-f2dc9cdb2f56
-- title:
--   Euler upper bound for a finite planar drawing
-- statement:
--   Every finite simple graph with the given crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. This is the planar Euler upper bound and applies whether or not the graph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c39276d2_5642_44b6_8869_8a52171f67f2_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
