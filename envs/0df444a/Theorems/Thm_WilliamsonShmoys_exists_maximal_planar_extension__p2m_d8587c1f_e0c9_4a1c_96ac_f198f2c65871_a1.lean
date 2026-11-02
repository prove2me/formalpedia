-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:03:23.540001+00:00
-- url     : https://prove2.me/theorems/4c05d890-938f-4efb-8ed0-8ebcd46f49c1
-- title:
--   Existence of an edge-maximal planar extension
-- statement:
--   Every connected graph with a crossing-free drawing on a finite vertex set has a connected planar supergraph on that same vertex set that has no strictly larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_d8587c1f_e0c9_4a1c_96ac_f198f2c65871_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) [DecidableRel N.Adj]
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hconn : N.Connected) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V, P ≤ Q →
        WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P := by sorry
