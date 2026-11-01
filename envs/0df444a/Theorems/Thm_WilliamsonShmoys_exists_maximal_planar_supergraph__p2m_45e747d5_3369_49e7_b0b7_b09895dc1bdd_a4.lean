-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:50:10.281191+00:00
-- url     : https://prove2.me/theorems/26ee7f91-8c6b-4630-b276-c962aab75208
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under drawable edge extensions and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ N : SimpleGraph V,
      (∀ u v, K.Adj u v → N.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      K.edgeFinset.card ≤ N.edgeSet.ncard ∧
      ∀ P : SimpleGraph V,
        (∀ u v, N.Adj u v → P.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn P →
        ∀ u v, P.Adj u v → N.Adj u v := by sorry
