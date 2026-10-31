-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_completion__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
-- name    : WilliamsonShmoys.planar_connected_completion__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:39:05.27048+00:00
-- url     : https://prove2.me/theorems/f6468396-3527-4419-8a9e-63046a838de6
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   This child removes the work of handling disconnected input from the parent. Starting from the supplied vertex points and nonintersecting arcs, connect drawing components through the complement, adding edges while preserving the drawing. The fixed vertex type preserves the vertex count, and the edge inclusion gives the edge-count monotonicity used by the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_completion__p2m_293782c6_00d7_4355_8c95_0afa44404fcb_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G) : ∃ H : SimpleGraph V, G.edgeSet ⊆ H.edgeSet ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected := by sorry
