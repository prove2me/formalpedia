-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1
-- name    : WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:59:19.084911+00:00
-- url     : https://prove2.me/theorems/8c76e379-80ae-42b0-9833-01d577d06e92
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs, with edge count at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_has_maximal_supergraph__p2m_8bebbcb3_63fa_47e0_bd08_43c40080b6a9_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) : ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ M.edgeSet.ncard ≤ N.edgeSet.ncard ∧ (∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) := by sorry
