-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph_retry2
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:18:16.673802+00:00
-- url     : https://prove2.me/theorems/9564f01b-b29b-4389-9f25-1dccc551a797
-- title:
--   Triangulating a finite planar drawing
-- statement:
--   Extend any crossing-free drawing on at least three vertices to a planar supergraph on the same vertices with exactly 3|V|−6 edges. This isolates the geometric triangulation step while preserving all original edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V, L <= M /\
      WilliamsonShmoys.HasPlanarDrawingOn M /\
      (M.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
