-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- name    : WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:58.109818+00:00
-- url     : https://prove2.me/theorems/6dfd0e85-ae5a-4e02-9c9b-5863f1785ef0
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs. The lower bound on the number of vertices is kept to match the parent, though this extension argument does not need it. Prove this by taking a drawable supergraph with the largest finite edge set; any strict drawable supergraph would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_maximal__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
