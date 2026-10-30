-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- name    : WilliamsonShmoys.planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:21.739297+00:00
-- url     : https://prove2.me/theorems/73ed4f8c-02a7-4393-b207-bffb2b107820
-- title:
--   Maximum-edge drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices whose edge count is at least that of every drawable supergraph of it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_maximal_planar_supergraph__p2m_5aab7b66_88f9_4907_8957_a5a3c4b4addc_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧ (∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W.edgeSet.ncard ≤ U.edgeSet.ncard) := by sorry
