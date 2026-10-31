-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- name    : WilliamsonShmoys.planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:45.616332+00:00
-- url     : https://prove2.me/theorems/8f444d1d-7358-42ec-8ec7-a42681e017e2
-- title:
--   Connected planar spanning extension
-- statement:
--   Every finite drawable simple graph has a connected drawable supergraph on the same vertex type, with at least as many edges. A proof can connect embedded components by routing new arcs through faces while avoiding the existing drawing except at the endpoints.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_spanning_connected_extension__p2m_b041ba7e_9475_4324_b141_7c04552295c3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.Connected ∧ HasPlanarDrawingOn K := by
  sorry
