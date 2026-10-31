-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:36:17.144483+00:00
-- url     : https://prove2.me/theorems/977ef0e9-2b10-4ce9-abb8-e8741d8c6875
-- title:
--   Connect the components of a planar drawing by added edges
-- statement:
--   Every finite graph with the specified crossing-free drawing has a connected planar supergraph on the same vertex type. When the drawing is already connected, choose H = K; otherwise add edges between components along noncrossing arcs. No vertex or drawing-cardinality hypotheses are added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_a2ea7bef_e32d_429b_9bbe_071fb272fdb7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
