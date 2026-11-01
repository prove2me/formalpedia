-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:48.92348+00:00
-- url     : https://prove2.me/theorems/06aa9184-ad05-46a0-aba1-f0ef97c506a7
-- title:
--   Connect components of a planar drawing with at least three vertices
-- statement:
--   For a finite graph on at least three vertices with a crossing-free drawing, there is a connected graph on the same vertex type that still has a crossing-free drawing and has at least as many edges. The size hypothesis rules out the empty-vertex counterexample to the earlier unrestricted augmentation claim. A proof route is to repeatedly join distinct embedded components by an arc through the complement and add the corresponding edge. The remaining work is to formalize that geometric construction for the given arc-based drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Connected ∧
      M.edgeSet.ncard <= H.edgeSet.ncard := by
  sorry
