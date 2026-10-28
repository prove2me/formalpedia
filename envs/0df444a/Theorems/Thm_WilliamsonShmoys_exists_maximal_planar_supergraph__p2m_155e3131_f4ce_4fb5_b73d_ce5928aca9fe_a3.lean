-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:53.314503+00:00
-- url     : https://prove2.me/theorems/4f41cab0-748e-4625-bdfe-c6316c755536
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on a fixed finite ordered vertex type has a drawable supergraph whose edge count is maximal among drawable supergraphs on that type. This removes the finite optimization step from the parent. A proof can use finiteness of the set of simple graphs on V: restrict to those containing M and admitting a drawing, note that M belongs to this set, and select a graph maximizing edge-set cardinality. The claim needs no lower bound on the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_155e3131_f4ce_4fb5_b73d_ce5928aca9fe_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
