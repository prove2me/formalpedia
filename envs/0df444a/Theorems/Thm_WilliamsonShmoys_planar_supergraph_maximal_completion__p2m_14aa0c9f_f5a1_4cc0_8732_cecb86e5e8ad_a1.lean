-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:38:10.75811+00:00
-- url     : https://prove2.me/theorems/3d4ff1fe-3e58-4c2b-a93a-6a199c5bf66b
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same ordered vertex type that is inclusion-maximal among drawable supergraphs. This follows by maximizing edge count over the finite set of supergraphs containing G; any drawable strict supergraph would have more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_completion__p2m_14aa0c9f_f5a1_4cc0_8732_cecb86e5e8ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists (fun K : SimpleGraph V =>
      G <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      forall H : SimpleGraph V, K <= H -> WilliamsonShmoys.HasPlanarDrawingOn H -> H <= K) := by
  sorry
