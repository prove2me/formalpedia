-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- name    : WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:23.684874+00:00
-- url     : https://prove2.me/theorems/faad2303-0a65-471d-a30c-3c1398903a00
-- title:
--   Connected planar graph edge bound
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This isolates the Euler and triangulation argument; the remaining core is deriving the bound from the geometric drawing, including bridge cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : HasPlanarDrawingOn L) (hLconn : L.Connected) (hV : 3 ≤ Fintype.card V) : L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
