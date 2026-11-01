-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:45.293135+00:00
-- url     : https://prove2.me/theorems/e1cd0124-e641-4ece-baff-4e3ebf9bbef8
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that admits no proper drawable supergraph. This removes the finite maximal-choice step from the parent. Independently, enumerate the finitely many simple graphs on `V` extending `K` that have a drawing and choose one with the largest edge-set cardinality; any drawable extension of that choice is also in the finite family, so maximal cardinality forces equality. No lower bound on `card V` is needed here, including when `V` is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_exists__p2m_cc6eda38_1b75_4537_8542_c84b46a8d9a9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ L : SimpleGraph V, H ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = H := by sorry
