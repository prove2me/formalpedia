-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_has_maximum_edges__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
-- name    : WilliamsonShmoys.inclusion_maximal_planar_has_maximum_edges__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:46.582448+00:00
-- url     : https://prove2.me/theorems/ba4159d3-5323-4426-8c82-d674db3cc476
-- title:
--   An inclusion-maximal drawable graph has maximum edge count
-- statement:
--   An inclusion-maximal drawable simple graph on a finite vertex set has at least as many edges as any drawable simple graph on that set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.inclusion_maximal_planar_has_maximum_edges__p2m_78cb0e01_1105_4561_a4db_7810010c8df8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (dQ : DecidableRel Q.Adj)
    (hQ : HasPlanarDrawingOn Q)
    (hmaximal : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      HasPlanarDrawingOn K → Q ≤ K → K = Q)
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : HasPlanarDrawingOn K) :
    letI : DecidableRel Q.Adj := dQ
    letI : DecidableRel K.Adj := dK
    Q.edgeFinset.card ≤ K.edgeFinset.card := by sorry
