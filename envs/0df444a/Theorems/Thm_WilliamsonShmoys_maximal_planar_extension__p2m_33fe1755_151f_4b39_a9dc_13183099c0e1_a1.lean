-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:19:55.531423+00:00
-- url     : https://prove2.me/theorems/27ddd0de-bda4-4766-bea7-58dc136f6100
-- title:
--   Extend a planar drawing to an edge-maximal planar supergraph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set that has no strictly larger planar supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_33fe1755_151f_4b39_a9dc_13183099c0e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V,
          M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
