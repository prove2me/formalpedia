-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- name    : WilliamsonShmoys.planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:27:46.102668+00:00
-- url     : https://prove2.me/theorems/6fcd0654-d3bd-446e-857f-90e55ba543f2
-- title:
--   Edge bound for maximal drawable graphs
-- statement:
--   For the exact drawing predicate, every inclusion-maximal drawable graph on at least three vertices has at least `3n - 6` edges. The intended independent proof route is to use maximality to obtain a triangulated plane embedding, then derive the bound from Euler's formula and edge-face incidence counting. This child retains the size threshold and does not assume the graph is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_augmentation_maximal_edge_bound__p2m_0835c3dc_b66c_4223_9284_2bc5bd7f2cf4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
     3 * Fintype.card V - 6 ≤ L.edgeFinset.card) := by sorry
