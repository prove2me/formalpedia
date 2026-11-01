-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:42.585359+00:00
-- url     : https://prove2.me/theorems/f0214461-761b-4faf-8b05-0b3f8d9a6a85
-- title:
--   An inclusion-maximal drawable supergraph exists
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that has no strict drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_inclusion_maximal_drawable_supergraph__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) :
    ∃ (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj),
      HasPlanarDrawingOn Q ∧ G ≤ Q ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K → Q ≤ K → K = Q) := by sorry
