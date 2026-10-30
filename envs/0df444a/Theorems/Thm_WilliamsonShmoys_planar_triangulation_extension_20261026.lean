-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_20261026
-- name    : WilliamsonShmoys.planar_triangulation_extension_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:57:54.428991+00:00
-- url     : https://prove2.me/theorems/df417363-6bd6-4765-aff0-a0f61b309e33
-- title:
--   Triangulation extension for a drawable graph
-- statement:
--   Every graph with a planar drawing on at least three vertices is contained in a planar supergraph on the same vertex type whose edge count is exactly 3|V|−6. This isolates the triangulation-completion and Euler-formula work; the parent applies maximality to identify the extension with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, J ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  sorry
