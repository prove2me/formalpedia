-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_glue_across_edge_free_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
-- name    : WilliamsonShmoys.planar_drawing_glue_across_edge_free_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:08:25.671239+00:00
-- url     : https://prove2.me/theorems/4ee156d7-cbac-4467-a134-5894bac4651f
-- title:
--   Drawings glue across an edge-free cut with a new joining edge
-- statement:
--   If a graph has a crossing-free drawing and no edges cross a cut, then it has a crossing-free supergraph on the same vertices that includes an edge between any chosen vertices on opposite sides. This replaces the parent-specific bridge claim with a reusable cut-gluing result. A proof can restrict the drawing to each side, normalize the drawings to expose the chosen vertices, place the drawings in separate regions, and connect those vertices by an arc in the exterior. The remaining work is to formalize the normalization and check all arc conditions in the packaged drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_glue_across_edge_free_cut__p2m_41ac2ad2_1442_40d5_933f_adb24d67ad24_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (S : Set V)
    (u v : V)
    (hu : u ∈ S)
    (hv : v ∉ S)
    (hCut : ∀ a b : V, a ∈ S → b ∉ S → ¬ G.Adj a b) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧ G ≤ H ∧ H.Adj u v := by sorry
