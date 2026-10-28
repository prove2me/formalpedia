-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_drawable_strict_supergraph_of_unreachable_pair
-- name    : WilliamsonShmoys.exists_drawable_strict_supergraph_of_unreachable_pair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T16:33:08.388824+00:00
-- url     : https://prove2.me/theorems/ba304637-c9f1-44fe-8544-a78216d3e472
-- title:
--   An unreachable pair can be joined while preserving drawability
-- statement:
--   Given a drawable finite graph and two vertices in different connected components, there is a drawable strict supergraph on the same vertices that contains the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_drawable_strict_supergraph_of_unreachable_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hUnreach : Not (G.Reachable u v)) :
    Exists fun H : SimpleGraph V =>
      And (G <= H)
        (And (WilliamsonShmoys.HasPlanarDrawingOn H) (Not (H <= G))) := by
  sorry
