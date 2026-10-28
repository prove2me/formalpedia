-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_exists_for_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_exists_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:31:17.919586+00:00
-- url     : https://prove2.me/theorems/89e789ca-77bb-4467-a2ef-9102df18ca41
-- title:
--   Existence of a maximal drawable supergraph for edge counting
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type is contained in a drawable graph maximal under edge inclusion. This child removes the completion step from the parent without requiring a vertex-count lower bound. A direct proof route is to consider the finite nonempty set of drawable supergraphs of S and choose an inclusion-maximal member; finiteness gives termination, and S witnesses nonemptiness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_exists_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      (∀ {u v}, S.Adj u v → T.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      (∀ U : SimpleGraph V,
        (∀ {u v}, T.Adj u v → U.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn U →
        ∀ {u v}, U.Adj u v → T.Adj u v) := by sorry
