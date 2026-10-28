-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawable_supergraph_exists_a0798f51_6e18_4401_9598_620a32b64bfd
-- name    : WilliamsonShmoys.planar_drawable_supergraph_exists_a0798f51_6e18_4401_9598_620a32b64bfd
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:29:55.987386+00:00
-- url     : https://prove2.me/theorems/c5029ef8-8cae-415d-9dd0-b854edc13f96
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph on the same vertices with no strictly larger drawable supergraph. The argument maximizes edge count among the finitely many drawable supergraphs containing the original graph; no lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawable_supergraph_exists_a0798f51_6e18_4401_9598_620a32b64bfd
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
        (forall N : SimpleGraph V, M <= N ->
          WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) := by sorry
