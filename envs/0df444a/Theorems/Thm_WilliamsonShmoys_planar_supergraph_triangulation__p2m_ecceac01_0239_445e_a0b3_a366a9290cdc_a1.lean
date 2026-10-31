-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:28:20.905304+00:00
-- url     : https://prove2.me/theorems/d0ea3fbd-f04a-4b41-b21e-1f15e29cc103
-- title:
--   Triangulated planar supergraph extension
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices is a subgraph, on the same vertex set, of a drawn simple graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_ecceac01_0239_445e_a0b3_a366a9290cdc_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
