-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- name    : WilliamsonShmoys.planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:07:24.402745+00:00
-- url     : https://prove2.me/theorems/94f9dee3-44c3-4c29-a91e-073301a1623a
-- title:
--   Add a planar bridge to a disconnected drawing
-- statement:
--   Every disconnected finite graph with at least three vertices and a crossing-free drawing has a strictly larger drawable simple supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_bridge_step__p2m_9eedc9cb_93e3_43ae_9b38_877bad90d9bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊂ K.edgeFinset ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
