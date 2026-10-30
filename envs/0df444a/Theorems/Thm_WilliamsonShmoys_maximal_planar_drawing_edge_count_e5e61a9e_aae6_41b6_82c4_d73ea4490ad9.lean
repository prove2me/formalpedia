-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:33:33.48961+00:00
-- url     : https://prove2.me/theorems/54c304f3-08fc-4985-9132-3333cc3a1889
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A connected drawable simple graph on at least three vertices that is maximal under drawable edge-preserving supergraphs has exactly `3 * |V| - 6` edges. A proof proceeds by showing maximality forces triangular faces in a planar embedding, then applying Euler’s formula; the order bound covers the small cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_e5e61a9e_aae6_41b6_82c4_d73ea4490ad9
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
