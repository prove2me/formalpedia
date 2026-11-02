-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:41.268258+00:00
-- url     : https://prove2.me/theorems/b455b77e-ddaf-4a1e-8731-97164a818640
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among all drawable supergraphs. Choose a drawable supergraph containing the original graph with the largest edge set; any further drawable supergraph would also contain the original graph, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ R : SimpleGraph V,
        (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn R →
        R = Q) := by sorry
