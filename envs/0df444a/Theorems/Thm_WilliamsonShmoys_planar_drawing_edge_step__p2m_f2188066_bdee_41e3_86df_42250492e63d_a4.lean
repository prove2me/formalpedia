-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
-- name    : WilliamsonShmoys.planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T22:14:13.578201+00:00
-- url     : https://prove2.me/theorems/9d9cb92a-f3a3-4293-9fde-9f5016b5eceb
-- title:
--   A disconnected planar drawing admits a strict planar edge extension
-- statement:
--   Every disconnected finite graph with the supplied drawing predicate admits a strict edge-set extension on the same vertices that still has the drawing predicate. This is the geometric core: prove suitable planar embedding and separation facts that yield an added edge whose arc satisfies the endpoint, injectivity, vertex avoidance, and edge-intersection conditions in the definition. Disconnectedness excludes the empty and singleton cases under the usual graph connectivity predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_step__p2m_f2188066_bdee_41e3_86df_42250492e63d_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hdisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊂ H.edgeSet ∧ HasPlanarDrawingOn H := by sorry
