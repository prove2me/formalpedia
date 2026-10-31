-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:19:28.747836+00:00
-- url     : https://prove2.me/theorems/8fae69ca-ae24-46cb-a1af-2dc3b1fd2851
-- title:
--   Maximal drawable extension on a fixed vertex type
-- statement:
--   Every drawable finite simple graph on a fixed finite vertex type is contained in a drawable graph that is maximal among drawable supergraphs; its edge count is at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6301d38c_0224_4362_a676_de729a46b58e_a3 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) : ∃ K : SimpleGraph V, N ≤ K ∧ N.edgeSet.ncard ≤ K.edgeSet.ncard ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
