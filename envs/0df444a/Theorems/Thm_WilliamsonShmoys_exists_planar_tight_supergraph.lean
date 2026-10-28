-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_tight_supergraph
-- name    : WilliamsonShmoys.exists_planar_tight_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:09:25.153167+00:00
-- url     : https://prove2.me/theorems/454b9bfe-ae40-4745-b185-30d9ca26acee
-- title:
--   Planar augmentation to the tight edge count
-- statement:
--   Every finite simple graph with a planar drawing and at least three vertices is contained in a planar graph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_tight_supergraph {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
