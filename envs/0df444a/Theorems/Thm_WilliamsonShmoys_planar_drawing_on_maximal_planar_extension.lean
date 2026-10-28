-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_planar_extension
-- name    : WilliamsonShmoys.planar_drawing_on_maximal_planar_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:01:40.075258+00:00
-- url     : https://prove2.me/theorems/a3b6f954-e9f0-4fb3-b9f3-f509bb7d59e4
-- title:
--   A planar drawing extends to an inclusion maximal planar supergraph
-- statement:
--   Every finite planar-drawable graph on at least three vertices has a planar-drawable supergraph on the same vertex set that is inclusion maximal among planar-drawable supergraphs. This removes the finite edge-maximization step from the parent. Prove it by considering the finite collection of edge sets on `V` whose graphs admit a planar drawing, selecting one containing `G` with the largest number of edges, and observing that any strict supergraph has more edges. The cardinality assumption is harmless here and is retained to align with the parent; the construction itself also works for smaller finite vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_on_maximal_planar_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ (L : SimpleGraph V), K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by
  sorry
