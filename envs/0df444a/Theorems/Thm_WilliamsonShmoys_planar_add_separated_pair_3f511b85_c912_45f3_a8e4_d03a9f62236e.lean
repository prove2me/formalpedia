-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- name    : WilliamsonShmoys.planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:43:02.090456+00:00
-- url     : https://prove2.me/theorems/427029e2-17da-486a-b6cd-191877c3bdf7
-- title:
--   A planar drawing can join vertices in different components
-- statement:
--   Given the packaged planar drawing of a finite graph and two distinct vertices in different reachability components, add an edge between them and produce a planar drawing of the enlarged graph with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_separated_pair_3f511b85_c912_45f3_a8e4_d03a9f62236e
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (huv : u ≠ v)
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ G' : SimpleGraph V, G ≤ G' ∧
      WilliamsonShmoys.HasPlanarDrawingOn G' ∧
      G.edgeSet.ncard < G'.edgeSet.ncard := by sorry
