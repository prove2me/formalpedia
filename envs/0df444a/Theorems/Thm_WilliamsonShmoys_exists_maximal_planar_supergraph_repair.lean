-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_repair
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:30:50.622848+00:00
-- url     : https://prove2.me/theorems/4348f77f-f17b-47c4-ab60-498739e75522
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type is contained in a drawable supergraph on that same type that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ T : SimpleGraph V, R ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U →
        WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by sorry
