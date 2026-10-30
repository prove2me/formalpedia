-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- name    : WilliamsonShmoys.planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:31:11.839352+00:00
-- url     : https://prove2.me/theorems/3d3a53f5-6da9-483c-b0e6-94f0720675a5
-- title:
--   Maximal drawable supergraph completion
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is maximal under drawable supergraph inclusion and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K ≤ H) := by sorry
