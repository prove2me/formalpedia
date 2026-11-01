-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:46:16.898214+00:00
-- url     : https://prove2.me/theorems/2a77e1c0-132e-4864-a8ba-ceda5e75c647
-- title:
--   Maximal planar extension and edge count
-- statement:
--   Every connected simple graph with at least three vertices that has a crossing-free drawing extends, on the same vertex set, to a simple planar graph with exactly 3n−6 edges; the extension contains all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_ff0df929_a528_472b_801c_6c58169000bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
