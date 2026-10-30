-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:05.228583+00:00
-- url     : https://prove2.me/theorems/9eedc9cb-93e3-43ae-9b38-877bad90d9bc
-- title:
--   Connect a drawn planar graph by adding edges
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a connected simple planar supergraph on the same vertex type, with its edge set containing the original edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_03ccc876_b6bf_43b7_928a_d41b56ffed25_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
