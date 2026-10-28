-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- name    : WilliamsonShmoys.planar_edge_count_maximal_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:22:20.016071+00:00
-- url     : https://prove2.me/theorems/ebae70db-5b94-4cc9-9ad3-f4e3267603f3
-- title:
--   Maximal drawable extension on the same vertices
-- statement:
--   Extend any drawable graph on at least three vertices to a drawable graph on the same vertices that contains it, has at least as many edges, and is maximal among drawable supergraphs. This handles disconnected inputs. An independent proof route is to maximize edge count among the finite set of drawable supergraphs of L; any drawable graph containing that maximizer also contains L, so the maximum gives the stated maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_maximal_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ M : SimpleGraph V, L.edgeSet.ncard ≤ M.edgeSet.ncard ∧ L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ (∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) := by sorry
