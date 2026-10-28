-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T19:52:21.770998+00:00
-- url     : https://prove2.me/theorems/2e485127-4874-47b6-87d0-2ac03b17d3ec
-- title:
--   Maximal planar graphs meet the Euler edge bound from below
-- statement:
--   A drawable graph on at least three vertices that is maximal under edge inclusion has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_e5c3d806_69b9_4602_a0f9_34c482daacc9
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hZ : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V,
      LE.le Z W →
      WilliamsonShmoys.HasPlanarDrawingOn W →
      W = Z)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ Z.edgeSet.ncard := by sorry
