-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_extend_between_unreachable_vertices
-- name    : WilliamsonShmoys.planar_drawing_extend_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:53:39.934526+00:00
-- url     : https://prove2.me/theorems/e6fd6f9c-cb4e-40b6-bfa0-c7938957c670
-- title:
--   Extend a planar drawing between unreachable vertices
-- statement:
--   Given a crossing-free drawing and two distinct vertices in different connected components, extend the graph strictly while preserving the existence of a crossing-free drawing. The distinctness and unreachability hypotheses ensure the new connection can join separate components; the lemma also covers isolated vertices and does not require a lower bound on the total vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_extend_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (huv : u ≠ v) (hnot : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G < H ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
