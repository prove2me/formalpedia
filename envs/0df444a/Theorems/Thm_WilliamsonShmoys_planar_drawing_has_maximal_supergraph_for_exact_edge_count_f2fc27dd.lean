-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_exact_edge_count_f2fc27dd
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_exact_edge_count_f2fc27dd
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:21:07.166073+00:00
-- url     : https://prove2.me/theorems/d1a88d8b-7ea0-4c39-908d-4cff46f34ffd
-- title:
--   A drawable graph has a maximal drawable extension
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion. This removes the finite maximization step from the parent. A direct proof forms the finite nonempty family of drawable supergraphs of the input and selects an inclusion-maximal member; the input itself witnesses nonemptiness. No lower bound on the number of vertices is needed for this step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_exact_edge_count_f2fc27dd
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      ∃ hH : WilliamsonShmoys.HasPlanarDrawingOn H,
        ∀ K : SimpleGraph V, H ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
