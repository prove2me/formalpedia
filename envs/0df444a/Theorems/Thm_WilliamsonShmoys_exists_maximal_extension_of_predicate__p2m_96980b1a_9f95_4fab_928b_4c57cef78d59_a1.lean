-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:45:11.8658+00:00
-- url     : https://prove2.me/theorems/0de55c23-bd87-4d0a-a45b-3dee362a13be
-- title:
--   Finite maximal extension for a graph predicate
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has a predicate-satisfying supergraph that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_predicate__p2m_96980b1a_9f95_4fab_928b_4c57cef78d59_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (L : SimpleGraph V)
    (hL : P L) :
    ∃ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet ∧
      P M ∧
      ∀ N : SimpleGraph V,
        M.edgeSet ⊆ N.edgeSet →
        P N →
        N = M := by sorry
