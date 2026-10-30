-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- name    : WilliamsonShmoys.maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T21:33:56.391931+00:00
-- url     : https://prove2.me/theorems/c622ba0a-ed25-4519-a465-b7b81b14262c
-- title:
--   Maximal planar graphs are connected
-- statement:
--   A graph on a finite ordered vertex type that has a planar drawing and is maximal among planar supergraphs on those vertices is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_connected__p2m_8f6efc51_6e5d_41c5_9bd8_54beb0297e61_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.Connected := by sorry
