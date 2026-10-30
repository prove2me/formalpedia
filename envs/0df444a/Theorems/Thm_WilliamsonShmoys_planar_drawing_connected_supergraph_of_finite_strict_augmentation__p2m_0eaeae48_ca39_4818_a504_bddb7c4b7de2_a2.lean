-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:02:23.420404+00:00
-- url     : https://prove2.me/theorems/66a879c4-84d6-4004-bc56-1840fb928f38
-- title:
--   Iterate finite strict planar edge augmentations
-- statement:
--   This removes the iteration and termination work from the parent. The one-step premise preserves the original graph, preserves a drawing, and strictly increases the edge set whenever the current graph is disconnected. A proof route is finite induction or well-founded recursion on the number of edges still available in the finite set of possible vertex pairs; strict edge-set growth decreases that measure, and a terminal graph cannot be disconnected because the one-step premise would then supply another strict extension. It covers an initially connected graph by choosing it unchanged and retains the parent’s vertex-count hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph_of_finite_strict_augmentation__p2m_0eaeae48_ca39_4818_a504_bddb7c4b7de2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hStep : ∀ G : SimpleGraph V, L ≤ G → HasPlanarDrawingOn G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet ⊂ H.edgeSet) :
    ∃ H : SimpleGraph V, L ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
