-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
-- name    : WilliamsonShmoys.planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:52.151556+00:00
-- url     : https://prove2.me/theorems/d40c3a6b-3de6-46aa-9fd1-14fe5823e11e
-- title:
--   Transfer the connected planar edge bound to a subgraph
-- statement:
--   If a graph is a subgraph of a connected graph on the same finite vertex type, and the latter has a planar drawing, then the former satisfies the planar edge-count bound for at least three vertices. The proof uses the connected planar edge bound and monotonicity of edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_from_connected_extension__p2m_7a1738f6_5642_467f_b376_eb6ed4a76310_a1 {V : Type} [Fintype V] [LinearOrder V] (K H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hKH : K ≤ H) (hHconn : H.Connected) (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
