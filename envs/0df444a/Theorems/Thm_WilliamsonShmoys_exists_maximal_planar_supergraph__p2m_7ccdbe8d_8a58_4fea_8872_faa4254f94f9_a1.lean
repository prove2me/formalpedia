-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:27:43.26927+00:00
-- url     : https://prove2.me/theorems/3fd6c9d0-0bab-4295-96fe-9618d3abbf51
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Among drawable supergraphs of a given drawable finite graph on the same vertex type, there is one with maximum edge count. The proof route is finite maximization: the candidate set is nonempty because it contains the starting graph, and there are only finitely many simple graphs on a finite vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_7ccdbe8d_8a58_4fea_8872_faa4254f94f9_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
