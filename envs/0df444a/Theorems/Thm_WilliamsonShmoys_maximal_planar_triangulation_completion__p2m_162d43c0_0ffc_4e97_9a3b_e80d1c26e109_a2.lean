-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2
-- name    : WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:43:41.607186+00:00
-- url     : https://prove2.me/theorems/d4ca7189-9565-4817-b2d2-3ba34e6b1168
-- title:
--   Every drawable graph has a triangulated planar completion
-- statement:
--   Every finite ordered vertex type with at least three vertices and a graph satisfying the supplied crossing-free drawing predicate admits a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The child captures the topological completion and Euler-counting work. It preserves the lower bound needed at the three-vertex boundary; the parent then uses maximality to identify the completion with Q.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_triangulation_completion__p2m_162d43c0_0ffc_4e97_9a3b_e80d1c26e109_a2 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hDraw : HasPlanarDrawingOn Q) (hV : 3 ≤ Fintype.card V) : ∃ R : SimpleGraph V, Q.edgeSet ⊆ R.edgeSet ∧ HasPlanarDrawingOn R ∧ R.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
