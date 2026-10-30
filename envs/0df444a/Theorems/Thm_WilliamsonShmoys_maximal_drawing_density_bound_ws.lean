-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_density_bound_ws
-- name    : WilliamsonShmoys.maximal_drawing_density_bound_ws
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:12:04.978331+00:00
-- url     : https://prove2.me/theorems/48412bf5-a329-4db7-b424-9cabb8a15d56
-- title:
--   Density of a maximal planar drawing
-- statement:
--   A drawable graph that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges when there are at least three vertices. The proof route is to show every face is triangular, then use Euler’s formula and count face-edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_density_bound_ws {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) (hcard : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
