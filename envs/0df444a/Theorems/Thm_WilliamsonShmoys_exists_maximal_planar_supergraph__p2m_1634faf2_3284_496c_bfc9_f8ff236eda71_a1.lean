-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:08:09.648654+00:00
-- url     : https://prove2.me/theorems/4d0efdc8-eda6-4b5a-8ab7-95ef4eb53842
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, every drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_1634faf2_3284_496c_bfc9_f8ff236eda71_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L := by sorry
