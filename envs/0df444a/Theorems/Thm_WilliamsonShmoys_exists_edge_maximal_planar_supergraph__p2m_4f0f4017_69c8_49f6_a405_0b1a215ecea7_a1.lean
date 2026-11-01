-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:36:42.207688+00:00
-- url     : https://prove2.me/theorems/87ed5adb-82f3-488c-b808-7f2da9357c21
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Every connected graph with a planar drawing has a planar supergraph on the same finite vertex set that is maximal under planar edge-supergraph inclusion. This isolates the finite maximal-extension step; it follows by maximizing over the finite collection of simple graphs on the vertex set that contain the original graph and admit a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_4f0f4017_69c8_49f6_a405_0b1a215ecea7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hconn : L.Connected) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
