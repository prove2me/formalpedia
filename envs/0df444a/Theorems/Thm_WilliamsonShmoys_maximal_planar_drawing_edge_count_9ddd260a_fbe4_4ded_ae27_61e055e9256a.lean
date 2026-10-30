-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:46:50.304982+00:00
-- url     : https://prove2.me/theorems/1486de53-97d2-4054-97ff-9c698a0d5d77
-- title:
--   Edge count of a maximal finite planar drawing
-- statement:
--   An inclusion-maximal finite simple graph with a crossing-free drawing on a fixed vertex type of size at least three has exactly 3|V| − 6 edges. The size condition is needed for this formula; maximal drawable graphs on fewer vertices do not satisfy it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_9ddd260a_fbe4_4ded_ae27_61e055e9256a {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H) (hMaximal : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
