-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T07:44:09.877619+00:00
-- url     : https://prove2.me/theorems/6ef36ecb-af00-4630-a640-abae38d127e2
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph maximal among drawable supergraphs on that same vertex type. This removes the finite maximization step from the parent. Choose a drawable supergraph with greatest edge count; any drawable extension must then be below it. The hypotheses allow any finite vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_retry7_a6cc6ce2_4479_4e22_ad6e_c928f195198d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    Exists (fun M : SimpleGraph V =>
      And (LE.le K M)
        (And (WilliamsonShmoys.HasPlanarDrawingOn M)
          (forall N : SimpleGraph V, LE.le M N ->
            WilliamsonShmoys.HasPlanarDrawingOn N -> LE.le N M))) := by sorry
