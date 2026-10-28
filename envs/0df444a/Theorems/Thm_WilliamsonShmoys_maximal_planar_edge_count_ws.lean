-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ws
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ws
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:53:25.721992+00:00
-- url     : https://prove2.me/theorems/46b9406d-28b0-4c12-9dca-2b5ffb9cb81b
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple planar graph on at least three vertices that has no proper planar supergraph on the same vertex type has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_ws {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (K : SimpleGraph V), H ≤ K → HasPlanarDrawingOn K → K ≤ H) : H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
