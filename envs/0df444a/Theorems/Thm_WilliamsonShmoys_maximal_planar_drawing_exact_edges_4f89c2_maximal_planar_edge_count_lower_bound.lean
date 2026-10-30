-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edges_4f89c2_maximal_planar_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_maximal_planar_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:09:00.713986+00:00
-- url     : https://prove2.me/theorems/908c2f26-5cd5-44d2-a10d-524f6d39e41c
-- title:
--   Lower edge count for maximal planar drawings
-- statement:
--   A graph with the specified planar drawing that has no strict planar edge extension on the same vertex set has at least 3n − 6 edges. This removes the maximality-based lower-bound argument from the parent. For three vertices, maximality forces all three edges. For larger vertex sets, a proof route establishes the needed connectivity and face structure from maximality, including justified geometric edge additions where applicable, then uses Euler’s formula. The remaining core is proving those augmentation and face-structure facts for the exact arc predicate; arbitrary augmentation of disconnected drawings must not be assumed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edges_4f89c2_maximal_planar_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ S : SimpleGraph V, R.edgeSet ⊂ S.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn S) :
    3 * Fintype.card V - 6 <= R.edgeSet.ncard := by sorry
