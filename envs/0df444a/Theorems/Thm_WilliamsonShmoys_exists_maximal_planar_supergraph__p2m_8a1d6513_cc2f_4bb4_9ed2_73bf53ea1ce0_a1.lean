-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:31.590281+00:00
-- url     : https://prove2.me/theorems/074f37c1-44b5-4e2a-beb4-02cefa9615fb
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   A connected drawable graph on a finite vertex set has a drawable supergraph on the same vertices that is maximal under edge inclusion; the supergraph remains connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8a1d6513_cc2f_4bb4_9ed2_73bf53ea1ce0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hconn : H.Connected)
    (hH : HasPlanarDrawingOn H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      K.Connected ∧
      ∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset →
        HasPlanarDrawingOn G → G = K := by sorry
