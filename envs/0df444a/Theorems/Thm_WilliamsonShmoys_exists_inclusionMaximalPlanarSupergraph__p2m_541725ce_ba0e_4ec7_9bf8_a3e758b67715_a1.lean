-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- name    : WilliamsonShmoys.exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:01:31.332622+00:00
-- url     : https://prove2.me/theorems/58be6bd2-7b61-44ae-b8f6-153972a57451
-- title:
--   Finite inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal under edge inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusionMaximalPlanarSupergraph__p2m_541725ce_ba0e_4ec7_9bf8_a3e758b67715_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      K ≤ H ∧ HasPlanarDrawingOn H ∧
        ∀ (J : SimpleGraph V) (_ : DecidableRel J.Adj),
          H ≤ J → HasPlanarDrawingOn J → J ≤ H := by sorry
