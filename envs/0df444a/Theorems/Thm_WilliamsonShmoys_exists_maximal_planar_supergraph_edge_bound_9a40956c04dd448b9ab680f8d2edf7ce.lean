-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:50:10.477867+00:00
-- url     : https://prove2.me/theorems/0bc2d711-6d21-4f1a-a205-720142236a19
-- title:
--   Existence of a maximal drawable supergraph for the planar edge bound
-- statement:
--   Any drawable finite simple graph is contained in a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
    {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ K : SimpleGraph V,
      L ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V, K ≤ H →
        WilliamsonShmoys.HasPlanarDrawingOn H → H = K := by
  sorry
