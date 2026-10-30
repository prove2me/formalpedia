-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- name    : WilliamsonShmoys.planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:17.638992+00:00
-- url     : https://prove2.me/theorems/24784cbb-b8f6-4e91-b5ba-b51ad6a651ca
-- title:
--   Extend a planar graph to an inclusion-maximal planar graph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under graph inclusion. The size hypothesis is retained for the target application; the finite maximization argument itself does not require it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extension_to_edge_maximal__p2m_39010df6_155f_482f_b0d9_cdc5767f59fc_a1 {V : Type} [Fintype V] [LinearOrder V] (X : SimpleGraph V) (hX : WilliamsonShmoys.HasPlanarDrawingOn X) (hV : 3 ≤ Fintype.card V) : ∃ Y : SimpleGraph V, X ≤ Y ∧ WilliamsonShmoys.HasPlanarDrawingOn Y ∧ ∀ Z : SimpleGraph V, Y ≤ Z → WilliamsonShmoys.HasPlanarDrawingOn Z → Y = Z := by sorry
