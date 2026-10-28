-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count_for_augmentation
-- name    : WilliamsonShmoys.maximal_planar_euler_count_for_augmentation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:52:08.231334+00:00
-- url     : https://prove2.me/theorems/0c08120b-590f-482f-88d1-cccf74679dd8
-- title:
--   Euler edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable finite simple graph with at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_count_for_augmentation {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
