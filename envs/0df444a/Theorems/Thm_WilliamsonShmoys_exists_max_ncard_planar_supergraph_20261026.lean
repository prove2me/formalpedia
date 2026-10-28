-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_ncard_planar_supergraph_20261026
-- name    : WilliamsonShmoys.exists_max_ncard_planar_supergraph_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:14:23.830422+00:00
-- url     : https://prove2.me/theorems/edf0a911-2972-4709-ba55-576fbdd3bab0
-- title:
--   Maximum edge-set cardinality among drawable supergraphs
-- statement:
--   Among drawable supergraphs of L, select one whose finite edge set has maximum cardinality. The class contains L, and finite V allows only finitely many simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_ncard_planar_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, L ≤ N →
          WilliamsonShmoys.HasPlanarDrawingOn N →
            N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
