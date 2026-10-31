-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
-- name    : WilliamsonShmoys.planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:55:26.76399+00:00
-- url     : https://prove2.me/theorems/c77f60cb-52bf-4945-9bde-3c0cc2df12db
-- title:
--   Exact edge-count planar supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3n − 6 edges. The statement includes disconnected graphs and preserves all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, (∀ u v, G.Adj u v → K.Adj u v) ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
