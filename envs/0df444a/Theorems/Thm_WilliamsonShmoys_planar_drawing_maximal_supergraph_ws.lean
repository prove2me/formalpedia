-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_ws
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_ws
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:52:47.979994+00:00
-- url     : https://prove2.me/theorems/3fb2042d-c9c5-4de1-aaf2-6cbbf9be000b
-- title:
--   Finite maximal planar supergraph
-- statement:
--   Every finite planar graph on this vertex type is contained in a planar supergraph that is maximal among planar supergraphs of the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_ws {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) (hcard : 3 ≤ Fintype.card V) : ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ (K : SimpleGraph V), M ≤ K → HasPlanarDrawingOn K → K ≤ H := by sorry
