-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T16:37:25.932483+00:00
-- url     : https://prove2.me/theorems/174dd15f-b3d3-42a8-b09e-f69588d740c0
-- title:
--   A maximal planar graph is connected
-- statement:
--   An inclusion-maximal planar graph on a finite ordered vertex type is connected, for the given crossing-free drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) :
    L.Connected := by sorry
