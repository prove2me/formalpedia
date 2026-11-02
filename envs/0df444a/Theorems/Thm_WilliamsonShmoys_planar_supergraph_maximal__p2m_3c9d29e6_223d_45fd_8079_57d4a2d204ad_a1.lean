-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:45:32.24684+00:00
-- url     : https://prove2.me/theorems/78898e31-8773-419c-99b2-d8837842d221
-- title:
--   Extend a connected planar drawing to a maximal planar graph
-- statement:
--   A connected graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has a maximal planar supergraph on the same vertex set. Maximality means every planar supergraph on that vertex set is equal to it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hconn : L.Connected)
    (hL : HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L <= M ∧ HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V, M <= N → HasPlanarDrawingOn N → N = M) := by sorry
