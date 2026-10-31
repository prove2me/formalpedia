-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- name    : WilliamsonShmoys.planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:37:40.248005+00:00
-- url     : https://prove2.me/theorems/f0a217ce-e36a-4a37-a22b-74995ac97000
-- title:
--   A drawable graph extends to an inclusion-maximal drawable graph
-- statement:
--   Every graph with the supplied planar drawing has a drawable supergraph on the same finite vertex type that is maximal under subgraph inclusion, with edge count at least that of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawable_maximal_extension__p2m_2cc4f687_238d_40a3_a706_2eb34249ae45_a1
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun H : SimpleGraph V =>
      G <= H /\ WilliamsonShmoys.HasPlanarDrawingOn H /\
      G.edgeSet.ncard <= H.edgeSet.ncard /\
      (forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= H) := by
  sorry
