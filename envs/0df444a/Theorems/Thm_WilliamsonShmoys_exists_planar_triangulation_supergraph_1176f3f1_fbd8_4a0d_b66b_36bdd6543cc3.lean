-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:43:30.287532+00:00
-- url     : https://prove2.me/theorems/4156f0d3-9fff-4189-9682-5ebd921f7232
-- title:
--   Triangulated drawable supergraph on the fixed vertex set
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_1176f3f1_fbd8_4a0d_b66b_36bdd6543cc3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
