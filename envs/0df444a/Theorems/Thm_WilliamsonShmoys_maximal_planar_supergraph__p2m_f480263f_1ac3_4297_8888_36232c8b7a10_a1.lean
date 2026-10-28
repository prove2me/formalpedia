-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:16:30.358339+00:00
-- url     : https://prove2.me/theorems/618ab57c-8c6f-43fe-b3a5-e204e9382199
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on the finite vertex type has a drawable supergraph on that same type that has no strictly larger drawable supergraph. This is an independent finite-maximization step: maximize edge count among drawable supergraphs of M in the finite set of simple graphs on V, and use maximal edge count to obtain inclusion maximality. It removes the choice of a suitable maximal graph from the parent; it does not establish that graph's edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_f480263f_1ac3_4297_8888_36232c8b7a10_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    exists K : SimpleGraph V,
      M <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
        (forall L : SimpleGraph V, K <= L ->
          WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := by sorry
