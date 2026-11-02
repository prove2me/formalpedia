-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:33.620117+00:00
-- url     : https://prove2.me/theorems/350700c7-dd24-47f5-9bef-0db864652b8b
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion. This removes the finite graph-choice and maximality bookkeeping from the parent. The child follows by selecting a maximal element from the finite nonempty set of drawable supergraphs of M; the chosen graph is drawable and M itself witnesses nonemptiness. No cardinality lower bound is needed here.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_maximal_supergraph__p2m_e31b05a7_4e78_4789_8a19_ecdeedbcdfa7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
        ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N := by sorry
