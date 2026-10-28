-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:36:09.858003+00:00
-- url     : https://prove2.me/theorems/2dc95e23-48ce-43f4-a52f-ffabf6c9a7ec
-- title:
--   Maximal drawable supergraph on a finite vertex type
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertex type that is maximal under edge inclusion among drawable graphs on that type. No vertex-count assumption is needed. The independent proof route is finite maximization over drawable supergraphs containing M: this set is nonempty because it contains M, and SimpleGraph V has only finitely many edge sets. A supergraph containing a maximizer cannot be a strict extension, since it would have a larger edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension_3624186a_b460_4cf9_8afd_86ec1a2d5ee8
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn N)
        (And (Set.Subset M.edgeSet N.edgeSet)
          (forall K : SimpleGraph V,
            WilliamsonShmoys.HasPlanarDrawingOn K ->
            Set.Subset N.edgeSet K.edgeSet ->
            N.edgeSet = K.edgeSet)) := by sorry
