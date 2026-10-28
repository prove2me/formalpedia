-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:15:52.750584+00:00
-- url     : https://prove2.me/theorems/161f6941-f01f-43b2-9074-6786a3749498
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a fixed finite vertex type is contained in a drawable supergraph that has no proper drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_b3d3d4e0_653c_48d5_a9c6_646106519c2d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ P : SimpleGraph V, N ≤ P → HasPlanarDrawingOn P → P = N := by sorry
