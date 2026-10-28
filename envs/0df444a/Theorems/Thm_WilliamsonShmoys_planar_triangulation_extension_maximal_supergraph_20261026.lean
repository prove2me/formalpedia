-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_supergraph_20261026
-- name    : WilliamsonShmoys.planar_triangulation_extension_maximal_supergraph_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:04:23.341607+00:00
-- url     : https://prove2.me/theorems/1e03b559-281e-4aca-9102-12ecfb18f1ff
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same type which is maximal among drawable supergraphs under inclusion. The independent proof route is finite maximization over all qualifying simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_maximal_supergraph_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ L : SimpleGraph V, J ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ K : SimpleGraph V, L ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = L := by
  sorry
