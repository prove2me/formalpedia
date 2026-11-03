-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- name    : WilliamsonShmoys.maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:42:49.982205+00:00
-- url     : https://prove2.me/theorems/46bd3770-49b2-4c1a-90e5-69dd719cc31d
-- title:
--   A maximal drawable graph is connected
-- statement:
--   On at least three finite ordered vertices, a drawable graph maximal among drawable supergraphs is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_connected__p2m_078d72d1_c4b8_4d42_8ead_9d2688891836_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (hcard : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : forall L : SimpleGraph V, K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L <= K) : K.Connected := by sorry
