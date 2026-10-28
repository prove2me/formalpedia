-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_extension_279755a6_02cd_4483_9b65_417cbe6cd492
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_extension_279755a6_02cd_4483_9b65_417cbe6cd492
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:56:34.807511+00:00
-- url     : https://prove2.me/theorems/64d6e2a9-6ce4-4f08-9a88-0f6f4c7447d4
-- title:
--   Every drawable graph has a maximal drawable supergraph
-- statement:
--   On a finite vertex type, every drawable graph has an inclusion-maximal drawable supergraph on that same type. This removes the finite maximal-choice step from the parent and makes no edge-count claim. An independent proof route is to consider the finite set of simple graphs containing H, restrict to those with a drawing, and choose a maximal member. The argument does not require connectedness or a nonempty graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_extension_279755a6_02cd_4483_9b65_417cbe6cd492
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists K : SimpleGraph V,
      H <= K /\ WilliamsonShmoys.HasPlanarDrawingOn K /\
      (forall L : SimpleGraph V,
        K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) := by sorry
