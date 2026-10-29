-- Prove2me | Theorems.Thm_finite_planar_extension_max_edge_count__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- name    : finite_planar_extension_max_edge_count__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:48:54.097765+00:00
-- url     : https://prove2.me/theorems/50074e12-440f-499c-afbf-43ae85e24b38
-- title:
--   A planar graph has a maximum-edge planar extension
-- statement:
--   Among planar graphs on the finite vertex type that contain G, one has at least as many edges as every other such graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem finite_planar_extension_max_edge_count__p2m_8523885d_5a38_4a4c_a926_9e6dc9f2f875_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, G ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
