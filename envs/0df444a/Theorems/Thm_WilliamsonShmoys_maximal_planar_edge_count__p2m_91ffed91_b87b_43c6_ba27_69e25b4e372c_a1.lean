-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:12.22219+00:00
-- url     : https://prove2.me/theorems/3b1a98e5-f0d3-4027-b8f6-4e4c1f675a8e
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A connected maximal planar graph with at least three vertices has three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_91ffed91_b87b_43c6_ba27_69e25b4e372c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P →
      WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
