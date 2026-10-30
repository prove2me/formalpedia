-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:16:38.868815+00:00
-- url     : https://prove2.me/theorems/4d6b09f4-cc64-4c42-8df1-4b93fc74bb58
-- title:
--   Planar completion to a triangulated edge count
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. This isolates planar triangulation extension and Euler counting from the parent theorem’s maximality argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_sharp_edge_count__p2m_4dcc8868_a279_4e00_9c27_a17d1a75556d_a1 {V : Type} [Fintype V] [LinearOrder V] (U : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hU : HasPlanarDrawingOn U) : ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧ 3 * Fintype.card V - 6 = W.edgeSet.ncard := by sorry
