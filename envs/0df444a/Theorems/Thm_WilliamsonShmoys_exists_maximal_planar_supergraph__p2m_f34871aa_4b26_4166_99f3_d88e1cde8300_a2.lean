-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T05:54:38.402996+00:00
-- url     : https://prove2.me/theorems/0b2b689d-06fa-42eb-be13-4acf0d588c2a
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is maximal under graph inclusion among drawable supergraphs. This removes the finite-choice step from the parent: filter the finite set of simple graphs to drawable supergraphs of N, choose one with maximum edge count, and use finite strict inclusion to rule out a larger drawable supergraph. This argument does not require a lower bound on |V|, so it covers small and empty vertex types whenever the hypotheses hold. The remaining topological obligation is the edge count of a maximal drawing, handled by the second child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_f34871aa_4b26_4166_99f3_d88e1cde8300_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    Exists fun K : SimpleGraph V =>
      N <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K <= L → WilliamsonShmoys.HasPlanarDrawingOn L → L <= K := by sorry
