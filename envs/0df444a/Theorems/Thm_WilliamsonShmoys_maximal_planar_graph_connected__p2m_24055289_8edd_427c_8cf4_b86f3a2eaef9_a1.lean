-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T19:36:22.479573+00:00
-- url     : https://prove2.me/theorems/8beee850-18d5-4447-ad2e-5af0f49fac8d
-- title:
--   An inclusion-maximal drawable graph is connected
-- statement:
--   Any graph maximal under edge inclusion among graphs with a crossing-free drawing on the same finite ordered vertex type is connected. The empty and one-vertex boundary cases are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_24055289_8edd_427c_8cf4_b86f3a2eaef9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K ≤ H) :
    H.Connected := by sorry
