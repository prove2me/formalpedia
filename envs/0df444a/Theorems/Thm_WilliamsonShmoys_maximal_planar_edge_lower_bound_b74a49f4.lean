-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_b74a49f4
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_b74a49f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:14:15.891556+00:00
-- url     : https://prove2.me/theorems/3c24a379-7313-46d0-81a4-eaccdcda727e
-- title:
--   Maximal planar edge lower bound
-- statement:
--   An inclusion-maximal graph with a crossing-free drawing on at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
