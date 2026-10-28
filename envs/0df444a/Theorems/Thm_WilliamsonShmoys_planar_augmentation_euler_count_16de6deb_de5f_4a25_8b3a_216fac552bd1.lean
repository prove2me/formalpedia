-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1
-- name    : WilliamsonShmoys.planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T12:26:05.801516+00:00
-- url     : https://prove2.me/theorems/01e46af9-a098-4ef9-87c9-63ad085d1147
-- title:
--   Planar augmentation to the Euler edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable graph with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_euler_count_16de6deb_de5f_4a25_8b3a_216fac552bd1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) : ∃ M : SimpleGraph V, L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
