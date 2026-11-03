-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- name    : WilliamsonShmoys.planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:22.202311+00:00
-- url     : https://prove2.me/theorems/db85b882-89e6-4feb-9146-2311e309823a
-- title:
--   Planar edge bound for disconnected graphs
-- statement:
--   A disconnected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. Restrict the drawing to each connected component, apply the connected Euler bound to components of size at least three, and handle one- and two-vertex components directly. Each nonempty component of size v contributes at most 3v−3 edges; with at least two components, summing gives the claimed bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarEdgeBound_disconnected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
