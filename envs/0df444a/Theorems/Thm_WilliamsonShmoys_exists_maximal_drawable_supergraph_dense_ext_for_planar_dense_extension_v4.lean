-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_dense_ext_for_planar_dense_extension_v4
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_dense_ext_for_planar_dense_extension_v4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:26:59.186123+00:00
-- url     : https://prove2.me/theorems/daa39b08-4f07-482b-873c-1732b9175c22
-- title:
--   Existence of a maximal drawable supergraph for dense extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph that is maximal among drawable supergraphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_dense_ext_for_planar_dense_extension_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V, N <= P /\ WilliamsonShmoys.HasPlanarDrawingOn P /\
      forall Q : SimpleGraph V, P <= Q -> WilliamsonShmoys.HasPlanarDrawingOn Q -> Q <= P := by sorry
