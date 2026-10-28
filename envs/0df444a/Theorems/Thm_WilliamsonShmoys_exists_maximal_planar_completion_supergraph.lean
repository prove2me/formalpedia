-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_completion_supergraph
-- name    : WilliamsonShmoys.exists_maximal_planar_completion_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:07:10.056768+00:00
-- url     : https://prove2.me/theorems/4135435b-e0dd-44bd-9e62-8d3b8524bf33
-- title:
--   Finite maximal drawable supergraph for planar completion
-- statement:
--   Every drawable finite graph has a drawable supergraph that is inclusion-maximal among drawable graphs on the same vertex type. This isolates the finite maximization step; maximize edge-set cardinality among the finitely many drawable supergraphs containing the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_completion_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by
  sorry
