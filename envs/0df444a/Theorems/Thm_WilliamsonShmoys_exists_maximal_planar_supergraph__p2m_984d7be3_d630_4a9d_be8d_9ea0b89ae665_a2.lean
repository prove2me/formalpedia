-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:59:14.811534+00:00
-- url     : https://prove2.me/theorems/25b87190-3b29-4822-985e-83123c023c7e
-- title:
--   Existence of an edge-maximal planar supergraph
-- statement:
--   Extend the given planar graph to one that is maximal under edge inclusion among planar graphs on the same vertex type. The finite collection of simple graphs containing H gives a natural maximality argument once planarity is preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_984d7be3_d630_4a9d_be8d_9ea0b89ae665_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
