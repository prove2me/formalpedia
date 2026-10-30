-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edgeSet_ncard_ge
-- name    : WilliamsonShmoys.planar_maximal_edgeSet_ncard_ge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:04:48.108599+00:00
-- url     : https://prove2.me/theorems/c6b3eef8-ec5a-4f54-b60c-ecca42449d07
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   A connected planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_maximal_edgeSet_ncard_ge
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hconn : L.Connected)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
