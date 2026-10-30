-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- name    : WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:48:33.999023+00:00
-- url     : https://prove2.me/theorems/561cdf23-b328-4e27-9dce-aabc2761bd72
-- title:
--   Existence of a maximal planar extension
-- statement:
--   A connected graph with a crossing-free drawing has a connected planar supergraph on the same finite vertex type that is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_extension__p2m_85efdcf1_7002_4c36_9c3f_e040848917fe_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      H.Connected := by sorry
