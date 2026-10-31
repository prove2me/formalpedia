-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:02.986552+00:00
-- url     : https://prove2.me/theorems/aa8f027a-93b4-4926-a309-4c6509e6e203
-- title:
--   Planar simple graphs satisfy the triangulation edge upper bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has at most 3|V|−6 edges. This is the Euler-formula upper bound; disconnected components can first be joined in the plane, and the resulting graph can be augmented to a triangulation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_1cedfa43_e759_4304_8f59_175ee0ad0ade_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
