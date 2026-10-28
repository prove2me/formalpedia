-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_exists_maximal_supergraph
-- name    : WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_exists_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:00:40.618808+00:00
-- url     : https://prove2.me/theorems/a9aac548-58c0-4b26-a7d4-5e9dd2a17444
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same type that is maximal under inclusion. This removes the finite existence step from the parent: maximize edge count over drawable supergraphs, and observe that any proper extension has strictly more edges. The hypotheses preserve the original drawing and the fixed vertex type. An independent proof route is to encode graphs as edge subsets of the finite set of possible pairs and select a maximum among the drawable extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_exists_maximal_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists (fun K : SimpleGraph V =>
      And (H <= K) (And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (forall L : SimpleGraph V, K <= L ->
          WilliamsonShmoys.HasPlanarDrawingOn L -> L = K))) := by sorry
