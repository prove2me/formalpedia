-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_20261026
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:38:28.561299+00:00
-- url     : https://prove2.me/theorems/d4d41cf8-983e-46e8-b83e-ef07e0589bd0
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices with no proper drawable supergraph on the same vertex type has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
