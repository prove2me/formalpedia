-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_lower_edge_bound
-- name    : WilliamsonShmoys.planar_supergraph_lower_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:07:00.986187+00:00
-- url     : https://prove2.me/theorems/fe0de7c4-f667-4441-8034-68284632c890
-- title:
--   Planar graphs admit a dense drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices satisfying the planar lower edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_lower_edge_bound {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H ∧ G.edgeSet ⊆ H.edgeSet ∧ 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
