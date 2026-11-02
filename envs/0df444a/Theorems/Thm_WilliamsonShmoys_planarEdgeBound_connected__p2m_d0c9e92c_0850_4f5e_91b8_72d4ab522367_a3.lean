-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- name    : WilliamsonShmoys.planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:53:18.641063+00:00
-- url     : https://prove2.me/theorems/5781120e-0dd2-40db-ad87-76e7c8291b92
-- title:
--   Planar edge bound for connected graphs
-- statement:
--   A connected finite simple graph with a crossing-free drawing and at least three vertices has at most three times its vertex count minus six edges. This isolates the Euler and face-boundary counting argument. A proof route is to derive a plane embedding from the drawing, apply Euler’s formula, and count face-boundary incidences, handling bridges explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarEdgeBound_connected__p2m_d0c9e92c_0850_4f5e_91b8_72d4ab522367_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
