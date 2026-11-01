-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
-- name    : WilliamsonShmoys.finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:17.294621+00:00
-- url     : https://prove2.me/theorems/b2333537-9e91-4fe0-a355-0d6ef469faac
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that is maximal under edge inclusion among drawable graphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      (∀ u v, K.Adj u v → M.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph V,
        (∀ u v, M.Adj u v → N.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn N →
        (∀ u v, N.Adj u v → M.Adj u v)) := by sorry
