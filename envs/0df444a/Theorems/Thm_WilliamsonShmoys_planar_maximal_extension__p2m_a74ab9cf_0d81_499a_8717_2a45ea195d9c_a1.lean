-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- name    : WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:20.813364+00:00
-- url     : https://prove2.me/theorems/d8caa262-4f2a-4c35-a872-b5a837a56723
-- title:
--   Extend a connected planar graph to a maximal planar graph
-- statement:
--   A connected finite planar graph has a connected planar supergraph on the same vertices that admits no proper planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys_planar_maximal_extension__p2m_a74ab9cf_0d81_499a_8717_2a45ea195d9c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hconn : G.Connected) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.Connected ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
