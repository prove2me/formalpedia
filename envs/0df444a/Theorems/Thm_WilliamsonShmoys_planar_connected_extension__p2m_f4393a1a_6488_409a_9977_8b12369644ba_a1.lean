-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- name    : WilliamsonShmoys.planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:21.45436+00:00
-- url     : https://prove2.me/theorems/59915996-ba45-4a21-88d9-b94eab65d4da
-- title:
--   Connect a planar drawing without adding vertices
-- statement:
--   Any planar drawing on at least three vertices can be extended, on the same vertices, to a connected planar graph containing the original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_extension__p2m_f4393a1a_6488_409a_9977_8b12369644ba_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       N.edgeFinset.card ≤ K.edgeFinset.card) ∧
      K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
