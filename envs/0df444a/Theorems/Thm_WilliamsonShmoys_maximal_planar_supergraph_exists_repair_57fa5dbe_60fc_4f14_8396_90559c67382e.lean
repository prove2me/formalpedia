-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:40:24.314089+00:00
-- url     : https://prove2.me/theorems/e9c6732c-80d6-4bda-b98b-6b928fd96f03
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every graph with the supplied planar-drawing property has a supergraph on the same finite vertex type that is maximal among graphs with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists_repair_57fa5dbe_60fc_4f14_8396_90559c67382e
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          L <= M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
