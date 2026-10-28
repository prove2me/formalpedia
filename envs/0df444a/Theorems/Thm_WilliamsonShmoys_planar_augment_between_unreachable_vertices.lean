-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augment_between_unreachable_vertices
-- name    : WilliamsonShmoys.planar_augment_between_unreachable_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:29:47.014584+00:00
-- url     : https://prove2.me/theorems/3da72a7a-677e-49d0-b879-880f50974f18
-- title:
--   Join two unreachable vertices in a planar drawing
-- statement:
--   Given a planar drawing and two vertices in different connected components, one can add edges to obtain a strict planar supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augment_between_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ G ≠ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
