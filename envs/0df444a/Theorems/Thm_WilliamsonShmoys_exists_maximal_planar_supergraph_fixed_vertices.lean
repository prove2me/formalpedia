-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fixed_vertices
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:59:42.566038+00:00
-- url     : https://prove2.me/theorems/d8a26a52-eee6-40f9-9050-f6bbff07b4f0
-- title:
--   Existence of a maximal drawable supergraph on fixed vertices
-- statement:
--   Every drawable graph on a finite fixed vertex type has a drawable supergraph on that same type that is maximal among drawable supergraphs. Finiteness gives a proof route by maximizing the edge count over drawable supergraphs; a strict extension adds an edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M →
          WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by
  sorry
